extern crate smtrs;
extern crate llvm_ir;

use self::smtrs::composite::{Composite,OptRef,Transformation,Transf};
use self::smtrs::embed::{Embed};
use std::cmp::{Ordering,max};
use self::llvm_ir::datalayout::DataLayout;
use self::llvm_ir::types::{Type as LLVMType};
use std::collections::HashMap;
use std::hash::{Hash,Hasher};

pub trait Bytes : Composite {
    fn byte_width(&self) -> usize;
    fn extract_bytes<'a,Em : Embed>(OptRef<'a,Self>,Transf<Em>,usize,usize,&mut Em)
                                    -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>;
}

#[derive(PartialEq,Eq,Clone,Debug)]
pub enum MemObj<'a,V : Composite> {
    FreshObj(usize),
    ConstObj(&'a DataLayout,
             &'a llvm_ir::Constant,
             &'a LLVMType,
             &'a HashMap<String,LLVMType>),
    ValueObj(V)
}

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub struct MemSlice<'a,V : Composite>(Vec<MemObj<'a,V>>);

pub trait FromConst<'a> : Composite {
    fn from_const<'b,Em : Embed>(&'a DataLayout,
                                 &'a llvm_ir::Constant,
                                 &'a LLVMType,
                                 &'a HashMap<String,LLVMType>,
                                 &mut Em)
                                 -> Result<Option<(OptRef<'b,Self>,Transf<Em>)>,Em::Error>;
}

impl<'a,V : Composite> MemSlice<'a,V> {
    pub fn alloca<Em : Embed>(sz: usize,_: &mut Em) -> (Self,Transf<Em>) {
        (MemSlice(vec![MemObj::FreshObj(sz)]),
         Transformation::id(0))
    }
    pub fn is_free(&self) -> bool {
        false
    }
}

impl<'a,V : Bytes+FromConst<'a>> MemObj<'a,V> {
    pub fn num_elem(&self) -> usize {
        match self {
            &MemObj::FreshObj(_) => 0,
            &MemObj::ConstObj(_,_,_,_) => 0,
            &MemObj::ValueObj(ref v) => v.num_elem()
        }
    }
    pub fn as_value<'b,Em : Embed>(obj: OptRef<'b,Self>,
                                   inp: Transf<Em>,
                                   em: &mut Em)
                                -> Result<Option<(OptRef<'b,V>,Transf<Em>)>,Em::Error> {
        match obj {
            OptRef::Ref(&MemObj::FreshObj(_)) |
            OptRef::Owned(MemObj::FreshObj(_)) => Ok(None),
            OptRef::Ref(&MemObj::ConstObj(ref dl,ref c,ref tp,ref tps))
                => V::from_const(dl,c,tp,tps,em),
            OptRef::Owned(MemObj::ConstObj(dl,c,tp,tps))
                => V::from_const(dl,c,tp,tps,em),
            OptRef::Ref(&MemObj::ValueObj(ref v))
                => Ok(Some((OptRef::Ref(v),inp))),
            OptRef::Owned(MemObj::ValueObj(v))
                => Ok(Some((OptRef::Owned(v),inp)))
        }
    }
}

impl<'a,V : Bytes+FromConst<'a>+Clone> Composite for MemSlice<'a,V> {
    fn num_elem(&self) -> usize {
        self.0.iter().map(|obj| match *obj {
            MemObj::FreshObj(_) => 0,
            MemObj::ConstObj(_,_,_,_) => 0,
            MemObj::ValueObj(ref v) => v.num_elem()
        }).sum()
    }
    fn elem_sort<Em : Embed>(&self,pos: usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        let mut off = 0;
        for obj in self.0.iter() {
            match *obj {
                MemObj::FreshObj(_) => panic!("elem_sort called for MemObj::FreshObj"),
                MemObj::ConstObj(_,_,_,_) => panic!("elem_sort called for MemObj::ConstObj"),
                MemObj::ValueObj(ref v) => {
                    let sz = v.num_elem();
                    if pos < off+sz {
                        return v.elem_sort(pos-off,em)
                    }
                    off+=sz
                }
            }
        }
        panic!("Invalid index: {}",pos)
    }
    fn combine<'b,Em,FComb,FL,FR>(x: OptRef<'b,Self>,y: OptRef<'b,Self>,
                                  inp_x: Transf<Em>,inp_y: Transf<Em>,
                                  comb: &FComb,only_l: &FL,only_r: &FR,em: &mut Em)
                                  -> Result<Option<(OptRef<'b,Self>,Transf<Em>)>,Em::Error>
        where Em : Embed,
              FComb : Fn(Transf<Em>,Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FL : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FR : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error> {

        let mut pos_x = 0;
        let mut pos_y = 0;
        let mut off_x = 0;
        let mut off_y = 0;
        let mut nslice = Vec::with_capacity(max(x.as_ref().0.len(),y.as_ref().0.len()));
        let mut ninp = Vec::with_capacity(max(x.as_ref().0.len(),y.as_ref().0.len()));
        let mut cur_x : Option<(MemObj<V>,Transf<Em>)> = None;
        let mut cur_y : Option<(MemObj<V>,Transf<Em>)> = None;
        loop {
            let rcur_x = match cur_x {
                None => {
                    if pos_x >= x.as_ref().0.len() {
                        if let Some((obj,inp)) = cur_y {
                            off_y += inp.size();
                            nslice.push(obj);
                            ninp.push(inp);
                        }
                        nslice.extend_from_slice(&y.as_ref().0[pos_y..]);
                        ninp.push(Transformation::view(off_y,inp_y.size()-off_y,inp_y));
                        break
                    }
                    let res = x.as_ref().0[pos_x].clone();
                    let sz = res.num_elem();
                    let inp = Transformation::view(off_x,sz,inp_x.clone());
                    pos_x+=1;
                    off_x+=sz;
                    (res,inp)
                },
                Some(r) => r
            };
            let rcur_y = match cur_y {
                None => {
                    if pos_y >= y.as_ref().0.len() {
                        off_x += rcur_x.1.size();
                        nslice.push(rcur_x.0);
                        ninp.push(rcur_x.1);
                        nslice.extend_from_slice(&x.as_ref().0[pos_x..]);
                        ninp.push(Transformation::view(off_x,inp_x.size()-off_x,inp_x));
                        break
                    }
                    let res = y.as_ref().0[pos_y].clone();
                    let sz = res.num_elem();
                    let inp = Transformation::view(off_y,sz,inp_y.clone());
                    pos_y+=1;
                    off_y+=sz;
                    (res,inp)
                },
                Some(r) => r
            };
            match rcur_x.0 {
                MemObj::FreshObj(w1) => match rcur_y.0 {
                    MemObj::FreshObj(w2) => match w1.cmp(&w2) {
                        Ordering::Equal => {
                            nslice.push(MemObj::FreshObj(w1));
                            cur_x = None;
                            cur_y = None;
                        },
                        Ordering::Less => {
                            nslice.push(MemObj::FreshObj(w1));
                            cur_x = None;
                            cur_y = Some((MemObj::FreshObj(w2-w1),
                                          Transformation::id(0)));
                        },
                        Ordering::Greater => {
                            nslice.push(MemObj::FreshObj(w2));
                            cur_x = Some((MemObj::FreshObj(w1-w2),
                                          Transformation::id(0)));
                            cur_y = None;
                        }
                    },
                    MemObj::ConstObj(_,_,_,_) => return Ok(None),
                    MemObj::ValueObj(ref v2) => {
                        let w2 = v2.byte_width();
                        match w1.cmp(&w2) {
                            Ordering::Equal => {
                                nslice.push(MemObj::ValueObj(v2.clone()));
                                ninp.push(rcur_y.1);
                                cur_x = None;
                                cur_y = None;
                            },
                            Ordering::Less => match V::extract_bytes(OptRef::Ref(v2),rcur_y.1.clone(),0,w1,em)? {
                                None => return Ok(None),
                                Some((spl1,inp1)) => match V::extract_bytes(OptRef::Ref(v2),rcur_y.1,w1,v2.byte_width()-w1,em)? {
                                    None => return Ok(None),
                                    Some((spl2,inp2)) => {
                                        nslice.push(MemObj::ValueObj(spl1.as_obj()));
                                        ninp.push(inp1);
                                        cur_x = None;
                                        cur_y = Some((MemObj::ValueObj(spl2.as_obj()),inp2));
                                    }
                                }
                            },
                            Ordering::Greater => {
                                nslice.push(MemObj::ValueObj(v2.clone()));
                                ninp.push(rcur_y.1);
                                cur_x = Some((MemObj::FreshObj(w1-v2.byte_width()),
                                              Transformation::id(0)));
                                cur_y = None;
                            }
                        }
                    }
                },
                MemObj::ConstObj(dl,c,tp,tps) => match rcur_y.0 {
                    MemObj::FreshObj(_) => return Ok(None),
                    MemObj::ConstObj(_,nc,ntp,_) => if c==nc {
                        nslice.push(MemObj::ConstObj(dl,c,tp,tps));
                        cur_x = None;
                        cur_y = None;
                    } else {
                        let (v1,inp_v1) = match V::from_const(dl,c,tp,tps,em)? {
                            None => return Ok(None),
                            Some(r) => r
                        };
                        let (v2,inp_v2) = match V::from_const(dl,nc,ntp,tps,em)? {
                            None => return Ok(None),
                            Some(r) => r
                        };
                        let w1 = v1.as_ref().byte_width();
                        let w2 = v2.as_ref().byte_width();
                        match w1.cmp(&w2) {
                            Ordering::Equal => match V::combine(v1,
                                                                v2,
                                                                inp_v1,
                                                                inp_v2,
                                                                comb,only_l,only_r,em)? {
                                None => return Ok(None),
                                Some((nv,inp)) => {
                                    nslice.push(MemObj::ValueObj(nv.as_obj()));
                                    ninp.push(inp);
                                    cur_x = None;
                                    cur_y = None;
                                }
                            },
                            Ordering::Less => match V::extract_bytes(v2.to_ref(),inp_v2.clone(),0,w1,em)? {
                                None => return Ok(None),
                                Some((spl1,inp1)) => match V::extract_bytes(v2.to_ref(),inp_v2,w1,w2-w1,em)? {
                                    None => return Ok(None),
                                    Some((spl2,inp2)) => match V::combine(v1,spl1,
                                                                          inp_v1,inp1,
                                                                          comb,only_l,only_r,em)? {
                                        None => return Ok(None),
                                        Some((nv,inp)) => {
                                            nslice.push(MemObj::ValueObj(nv.as_obj()));
                                            ninp.push(inp);
                                            cur_x = None;
                                            cur_y = Some((MemObj::ValueObj(spl2.as_obj()),inp2));
                                        }
                                    }
                                }
                            },
                            Ordering::Greater => match V::extract_bytes(v1.to_ref(),inp_v1.clone(),0,w2,em)? {
                                None => return Ok(None),
                                Some((spl1,inp1)) => match V::extract_bytes(v1.to_ref(),inp_v1,w2,w1-w2,em)? {
                                    None => return Ok(None),
                                    Some((spl2,inp2)) => match V::combine(spl1,v2,
                                                                          inp1,inp_v2,
                                                                          comb,only_l,only_r,em)? {
                                        None => return Ok(None),
                                        Some((nv,inp)) => {
                                            nslice.push(MemObj::ValueObj(nv.as_obj()));
                                            ninp.push(inp);
                                            cur_x = Some((MemObj::ValueObj(spl2.as_obj()),inp2));
                                            cur_y = None;
                                        }
                                    }
                                }
                            }
                        }
                    },
                    MemObj::ValueObj(v2) => {
                        let inp_v2 = rcur_y.1;
                        let (v1,inp_v1) = match V::from_const(dl,c,tp,tps,em)? {
                            None => return Ok(None),
                            Some(r) => r
                        };
                        let w1 = v1.as_ref().byte_width();
                        let w2 = v2.byte_width();
                        match w1.cmp(&w2) {
                            Ordering::Equal => match V::combine(v1,
                                                                OptRef::Ref(&v2),
                                                                inp_v1,
                                                                inp_v2,
                                                                comb,only_l,only_r,em)? {
                                None => return Ok(None),
                                Some((nv,inp)) => {
                                    nslice.push(MemObj::ValueObj(nv.as_obj()));
                                    ninp.push(inp);
                                    cur_x = None;
                                    cur_y = None;
                                }
                            },
                            Ordering::Less => match V::extract_bytes(OptRef::Ref(&v2),inp_v2.clone(),0,w1,em)? {
                                None => return Ok(None),
                                Some((spl1,inp1)) => match V::extract_bytes(OptRef::Ref(&v2),inp_v2,w1,w2-w1,em)? {
                                    None => return Ok(None),
                                    Some((spl2,inp2)) => match V::combine(v1,spl1,
                                                                          inp_v1,inp1,
                                                                          comb,only_l,only_r,em)? {
                                        None => return Ok(None),
                                        Some((nv,inp)) => {
                                            nslice.push(MemObj::ValueObj(nv.as_obj()));
                                            ninp.push(inp);
                                            cur_x = None;
                                            cur_y = Some((MemObj::ValueObj(spl2.as_obj()),inp2));
                                        }
                                    }
                                }
                            },
                            Ordering::Greater => match V::extract_bytes(v1.to_ref(),inp_v1.clone(),0,w2,em)? {
                                None => return Ok(None),
                                Some((spl1,inp1)) => match V::extract_bytes(v1.to_ref(),inp_v1,w2,w1-w2,em)? {
                                    None => return Ok(None),
                                    Some((spl2,inp2)) => match V::combine(spl1,OptRef::Ref(&v2),
                                                                          inp1,inp_v2,
                                                                          comb,only_l,only_r,em)? {
                                        None => return Ok(None),
                                        Some((nv,inp)) => {
                                            nslice.push(MemObj::ValueObj(nv.as_obj()));
                                            ninp.push(inp);
                                            cur_x = Some((MemObj::ValueObj(spl2.as_obj()),inp2));
                                            cur_y = None;
                                        }
                                    }
                                }
                            }
                        }
                    }
                },
                MemObj::ValueObj(v1) => {
                    let w1 = v1.byte_width();
                    if let MemObj::FreshObj(w2) = rcur_y.0 {
                        match w1.cmp(&w2) {
                            Ordering::Equal => {
                                nslice.push(MemObj::ValueObj(v1.clone()));
                                ninp.push(rcur_x.1);
                                cur_x = None;
                                cur_y = None;
                            },
                            Ordering::Less => {
                                nslice.push(MemObj::ValueObj(v1.clone()));
                                ninp.push(rcur_x.1);
                                cur_x = None;
                                cur_y = Some((MemObj::FreshObj(w2-w1),
                                              Transformation::id(0)));
                            },
                            Ordering::Greater => match V::extract_bytes(OptRef::Ref(&v1),rcur_x.1.clone(),0,w2,em)? {
                                None => return Ok(None),
                                Some((spl1,inp1)) => match V::extract_bytes(OptRef::Ref(&v1),rcur_x.1,w2,w1-w2,em)? {
                                    None => return Ok(None),
                                    Some((spl2,inp2)) => {
                                        nslice.push(MemObj::ValueObj(spl1.as_obj()));
                                        ninp.push(inp1);
                                        cur_x = Some((MemObj::ValueObj(spl2.as_obj()),inp2));
                                        cur_y = None;
                                    }
                                }
                            }
                        }
                    } else if let Some((v2,inp_v2)) = MemObj::as_value(OptRef::Owned(rcur_y.0),rcur_y.1,em)? {
                        let w2 = v2.as_ref().byte_width();
                            match w1.cmp(&w2) {
                                Ordering::Equal => match V::combine(OptRef::Ref(&v1),
                                                                    v2,
                                                                    rcur_x.1,
                                                                    inp_v2,
                                                                    comb,only_l,only_r,em)? {
                                    None => return Ok(None),
                                    Some((nv,inp)) => {
                                        nslice.push(MemObj::ValueObj(nv.as_obj()));
                                        ninp.push(inp);
                                        cur_x = None;
                                        cur_y = None;
                                    }
                                },
                                Ordering::Less => match V::extract_bytes(v2.to_ref(),inp_v2.clone(),0,w1,em)? {
                                    None => return Ok(None),
                                    Some((spl1,inp1)) => match V::extract_bytes(v2.to_ref(),inp_v2,w1,w2-w1,em)? {
                                        None => return Ok(None),
                                        Some((spl2,inp2)) => match V::combine(OptRef::Ref(&v1),spl1,
                                                                              rcur_x.1,inp1,
                                                                              comb,only_l,only_r,em)? {
                                            None => return Ok(None),
                                            Some((nv,inp)) => {
                                                nslice.push(MemObj::ValueObj(nv.as_obj()));
                                                ninp.push(inp);
                                                cur_x = None;
                                                cur_y = Some((MemObj::ValueObj(spl2.as_obj()),inp2));
                                            }
                                        }
                                    }
                                },
                                Ordering::Greater => match V::extract_bytes(OptRef::Ref(&v1),rcur_x.1.clone(),0,w2,em)? {
                                    None => return Ok(None),
                                    Some((spl1,inp1)) => match V::extract_bytes(OptRef::Ref(&v1),rcur_x.1,w2,w1-w2,em)? {
                                        None => return Ok(None),
                                        Some((spl2,inp2)) => match V::combine(spl1,v2,
                                                                              inp1,inp_v2,
                                                                              comb,only_l,only_r,em)? {
                                            None => return Ok(None),
                                            Some((nv,inp)) => {
                                                nslice.push(MemObj::ValueObj(nv.as_obj()));
                                                ninp.push(inp);
                                                cur_x = Some((MemObj::ValueObj(spl2.as_obj()),inp2));
                                                cur_y = None;
                                            }
                                        }
                                    }
                                }
                            }
                    } else {
                        unreachable!()
                    }
                }
            }
        }
        Ok(Some((OptRef::Owned(MemSlice(nslice)),Transformation::concat(&ninp[..]))))
    }
}

impl<'a,V : Composite> Hash for MemObj<'a,V> {
    fn hash<H>(&self, state: &mut H)
        where H: Hasher {
        match self {
            &MemObj::FreshObj(sz) => {
                (0 as usize).hash(state);
                sz.hash(state);
            },
            &MemObj::ConstObj(_,ref c,ref tp,_) => {
                (1 as usize).hash(state);
                c.hash(state);
                tp.hash(state);
            },
            &MemObj::ValueObj(ref v) => {
                (2 as usize).hash(state);
                v.hash(state);
            }
        }
    }
}
