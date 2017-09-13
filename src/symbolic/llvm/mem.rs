extern crate smtrs;

use self::smtrs::composite::{Composite,OptRef,Transformation,Transf};
use self::smtrs::embed::{Embed};
use std::cmp::{Ordering,max};
use std::fmt::Debug;

pub trait Bytes : Composite {
    fn byte_width(&self) -> usize;
    fn extract_bytes<'a,Em : Embed>(OptRef<'a,Self>,Transf<Em>,usize,usize)
                                    -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>;
}

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub enum MemObj<V : Composite> {
    FreshObj(usize),
    ValueObj(V)
}

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub struct MemSlice<V : Composite>(Vec<MemObj<V>>);

impl<V : Composite> MemSlice<V> {
    pub fn alloca<Em : Embed>(sz: usize,em: &mut Em) -> (Self,Transf<Em>) {
        (MemSlice(vec![MemObj::FreshObj(sz)]),
         Transformation::id(0))
    }
    pub fn is_free(&self) -> bool {
        false
    }
}

impl<V : Bytes + Clone> Composite for MemSlice<V> {
    fn num_elem(&self) -> usize {
        self.0.iter().map(|obj| match *obj {
            MemObj::FreshObj(_) => 0,
            MemObj::ValueObj(ref v) => v.num_elem()
        }).sum()
    }
    fn elem_sort<Em : Embed>(&self,pos: usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        let mut off = 0;
        for obj in self.0.iter() {
            match *obj {
                MemObj::FreshObj(_) => {},
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
    fn combine<'a,Em,FComb,FL,FR>(x: OptRef<'a,Self>,y: OptRef<'a,Self>,
                                  inp_x: Transf<Em>,inp_y: Transf<Em>,
                                  comb: &FComb,only_l: &FL,only_r: &FR,em: &mut Em)
                                  -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>
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
                    let sz = match res {
                        MemObj::FreshObj(_) => 0,
                        MemObj::ValueObj(ref v) => v.num_elem()
                    };
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
                    let sz = match res {
                        MemObj::FreshObj(_) => 0,
                        MemObj::ValueObj(ref v) => v.num_elem()
                    };
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
                    MemObj::ValueObj(ref v2) => {
                        let w2 = v2.byte_width();
                        match w1.cmp(&w2) {
                            Ordering::Equal => {
                                nslice.push(MemObj::ValueObj(v2.clone()));
                                ninp.push(rcur_y.1);
                                cur_x = None;
                                cur_y = None;
                            },
                            Ordering::Less => match V::extract_bytes(OptRef::Ref(v2),rcur_y.1.clone(),0,w1)? {
                                None => return Ok(None),
                                Some((spl1,inp1)) => match V::extract_bytes(OptRef::Ref(v2),rcur_y.1,w1,v2.byte_width()-w1)? {
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
                MemObj::ValueObj(v1) => {
                    let w1 = v1.byte_width();
                    match rcur_y.0 {
                        MemObj::FreshObj(w2) => match w1.cmp(&w2) {
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
                            Ordering::Greater => match V::extract_bytes(OptRef::Ref(&v1),rcur_x.1.clone(),0,w2)? {
                                None => return Ok(None),
                                Some((spl1,inp1)) => match V::extract_bytes(OptRef::Ref(&v1),rcur_x.1,w2,w1-w2)? {
                                    None => return Ok(None),
                                    Some((spl2,inp2)) => {
                                        nslice.push(MemObj::ValueObj(spl1.as_obj()));
                                        ninp.push(inp1);
                                        cur_x = Some((MemObj::ValueObj(spl2.as_obj()),inp2));
                                        cur_y = None;
                                    }
                                }
                            }
                        },
                        MemObj::ValueObj(v2) => {
                            let w2 = v2.byte_width();
                            match w1.cmp(&w2) {
                                Ordering::Equal => match V::combine(OptRef::Ref(&v1),
                                                                    OptRef::Ref(&v2),
                                                                    rcur_x.1,
                                                                    rcur_y.1,
                                                                    comb,only_l,only_r,em)? {
                                    None => return Ok(None),
                                    Some((nv,inp)) => {
                                        nslice.push(MemObj::ValueObj(nv.as_obj()));
                                        ninp.push(inp);
                                        cur_x = None;
                                        cur_y = None;
                                    }
                                },
                                Ordering::Less => match V::extract_bytes(OptRef::Ref(&v2),rcur_y.1.clone(),0,w1)? {
                                    None => return Ok(None),
                                    Some((spl1,inp1)) => match V::extract_bytes(OptRef::Ref(&v2),rcur_y.1,w1,w2-w1)? {
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
                                Ordering::Greater => match V::extract_bytes(OptRef::Ref(&v1),rcur_x.1.clone(),0,w2)? {
                                    None => return Ok(None),
                                    Some((spl1,inp1)) => match V::extract_bytes(OptRef::Ref(&v1),rcur_x.1,w2,w1-w2)? {
                                        None => return Ok(None),
                                        Some((spl2,inp2)) => match V::combine(spl1,OptRef::Ref(&v2),
                                                                              inp1,rcur_y.1,
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
                    }
                }
            }
        }
        Ok(Some((OptRef::Owned(MemSlice(nslice)),Transformation::concat(&ninp[..]))))
    }
}
