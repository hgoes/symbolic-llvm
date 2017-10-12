extern crate smtrs;
extern crate llvm_ir;

use self::smtrs::composite::*;
use self::smtrs::embed::{Embed};
use self::smtrs::expr;
use std::cmp::{Ordering,max};
use self::llvm_ir::datalayout::DataLayout;
use self::llvm_ir::types::{Type as LLVMType};
use std::collections::HashMap;
use std::hash::{Hash,Hasher};
use super::pointer::Offset;
use std::fmt::Debug;
use std::fmt;

pub trait Bytes : Composite {
    fn byte_width(&self) -> usize;
    fn extract_bytes<'a,Em : Embed>(OptRef<'a,Self>,Transf<Em>,usize,usize,&mut Em)
                                    -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error> {
        Ok(None)
    }
    fn concat_bytes<'a,Em : Embed>(OptRef<'a,Self>,
                                   Transf<Em>,
                                   OptRef<'a,Self>,
                                   Transf<Em>,
                                   &mut Em)
                                   -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error> {
        Ok(None)
    }
}

#[derive(PartialEq,Eq,Clone)]
pub enum MemObj<'a,V> {
    FreshObj(usize),
    ConstObj(&'a DataLayout,
             &'a llvm_ir::Constant,
             &'a LLVMType,
             &'a HashMap<String,LLVMType>),
    ValueObj(V)
}

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub struct MemSlice<'a,V>(pub Vec<MemObj<'a,V>>);

pub trait FromConst<'a> : Composite {
    fn from_const<Em : Embed>(&'a DataLayout,
                              &'a llvm_ir::Constant,
                              &'a LLVMType,
                              &'a HashMap<String,LLVMType>,
                              &mut Em)
                              -> Result<Option<(Self,Transf<Em>)>,Em::Error>;
}

impl<'a,V : Debug> Debug for MemObj<'a,V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match *self {
            MemObj::FreshObj(ref sz) => f.debug_tuple("FreshObj")
                .field(sz).finish(),
            MemObj::ConstObj(_,ref c,ref tp,_) => f.debug_tuple("MemObj")
                .field(c).field(tp).finish(),
            MemObj::ValueObj(ref v) => f.debug_tuple("ValueObj")
                .field(v).finish()
        }
    }
}

impl<'a,V : Bytes+FromConst<'a>+Clone+Debug> MemSlice<'a,V> {
    pub fn alloca<Em : Embed>(sz: usize,_: &mut Em) -> (Self,Transf<Em>) {
        (MemSlice(vec![MemObj::FreshObj(sz)]),
         Transformation::id(0))
    }
    pub fn realloc(&mut self,sz: usize) {
        let csz = self.byte_width();
        if sz==csz {
            return
        }
        if sz < csz {
            panic!("Making slices smaller not yet supported")
        }
        self.0.push(MemObj::FreshObj(sz-csz))
    }
    pub fn is_free(&self) -> bool {
        false
    }
    pub fn byte_width(&self) -> usize {
        let mut bw = 0;
        for obj in self.0.iter() {
            bw+=obj.byte_width()
        }
        bw
    }
    pub fn read_static<'b,Em>(sl: OptRef<'b,Self>,
                              inp_sl: Transf<Em>,
                              off: usize,
                              len: usize,
                              em: &mut Em)
                              -> Result<Option<(OptRef<'b,V>,Transf<Em>)>,Em::Error>
        where Em : Embed {
        //println!("Reading at {} with len {} from {:#?}",off,len,sl.as_ref());
        let mut acc = 0;
        let vec = match sl {
            OptRef::Ref(ref rsl) => OptRef::Ref(&rsl.0),
            OptRef::Owned(rsl) => OptRef::Owned(rsl.0)
        };
        let mut it = vec_iter(vec,inp_sl);
        while let Some((obj,obj_inp)) = it.next() {
            let bw = obj.as_ref().byte_width();
            if off<acc+bw {
                if off==acc && bw==len {
                    return MemObj::as_value(obj,obj_inp,em)
                }
                if off-acc+len<=bw {
                    return match MemObj::as_value(obj,obj_inp,em)? {
                        None => panic!("Reading from uninitialized memory at {}, previous element {}",off,acc),//Ok(None),
                        Some((sobj,sobj_inp))
                            => V::extract_bytes(sobj,sobj_inp,off-acc,len,em)
                    }
                }
                let (start,inp_start) = {
                    match MemObj::as_value(obj,obj_inp,em)? {
                        None => panic!("Reading from uninitialized memory"),//return Ok(None),
                        Some((val0,val0_inp)) => if off==acc {
                            (val0,val0_inp)
                        } else {
                            match V::extract_bytes(val0,val0_inp,off-acc,bw+acc-off,em)? {
                                None => panic!("Failed to extract bytes"),//return Ok(None),
                                Some(res) => res
                            }
                        }
                    }
                };
                acc+=bw;
                let rest = len+acc-off;
                let mut cur = start;
                let mut cur_inp = inp_start;
                while let Some((obj,obj_inp)) = it.next() {
                    let bw = obj.as_ref().byte_width();
                    let (val,val_inp) = match MemObj::as_value(obj,obj_inp,em)? {
                        None => panic!("Reading from uninitialized memory"),//return Ok(None),
                        Some(res) => res
                    };
                    if rest<bw {
                        let (rval,rval_inp) = match V::extract_bytes(val,val_inp,0,rest,em)? {
                            None => panic!("Reading from uninitialized memory"),//return Ok(None),
                            Some(res) => res
                        };
                        return V::concat_bytes(cur,cur_inp,rval,rval_inp,em)
                    }
                    let (ncur,ncur_inp) = match V::concat_bytes(cur,cur_inp,val,val_inp,em)? {
                        None => panic!("Cannot concat bytes"),//return Ok(None),
                        Some(res) => res
                    };
                    cur = ncur;
                    cur_inp = ncur_inp;
                    acc+=bw;
                }
                return panic!("Overread")//Ok(None)
            }
            acc+=bw;
        }
        panic!("Overread") //Ok(None)
    }
    pub fn read<'b,Em : Embed>(sl: OptRef<'b,Self>,
                               inp_sl: Transf<Em>,
                               off: OptRef<'b,Offset>,
                               inp_off: Transf<Em>,
                               len: usize,
                               em: &mut Em)
                               -> Result<Option<(OptRef<'b,V>,Transf<Em>)>,Em::Error> {
        let (mult,stat_off) = (off.as_ref().0).0;
        match off.as_ref().1 {
            None => Self::read_static(sl,inp_sl,stat_off,len,em),
            Some(ref singleton) => {
                panic!("No dynamic reading!");
                let srt = singleton.0.kind();
                let (val0,inp_val0) = match Self::read_static(sl.to_ref(),inp_sl.clone(),stat_off,len,em)? {
                    None => return Ok(None),
                    Some(r) => r
                };
                let sz = sl.as_ref().byte_width();
                let mut cval = val0;
                let mut inp_cval = inp_val0;
                for i in 0..(sz-stat_off-len)/mult {
                    let idx = index_as_value(&srt,i);
                    let (rval,inp_rval) = match Self::read_static(sl.to_ref(),inp_sl.clone(),stat_off+i*mult,len,em)? {
                        None => return Ok(None),
                        Some(r) => r
                    };
                    let cond_fun = move |_:&[Em::Expr],_:usize,e: Em::Expr,em: &mut Em| {
                        let c = em.embed(expr::Expr::Const(idx.clone()))?;
                        em.eq(e,c)
                    };
                    let cond = Transformation::map_by_elem(Box::new(cond_fun),inp_off.clone());
                    let (nval,inp_nval) = match ite(cval,rval,cond,inp_cval,inp_rval,em)? {
                        None => return Ok(None),
                        Some(r) => r
                    };
                    cval = nval;
                    inp_cval = inp_nval;
                }
                Ok(Some((OptRef::Owned(cval.as_obj()),inp_cval)))
            }
        }
    }
    pub fn write_static<'b,Em : Embed>(&mut self,
                                       inp_sl: Transf<Em>,
                                       off: usize,
                                       val: OptRef<'b,V>,
                                       val_inp: Transf<Em>,
                                       em: &mut Em)
                                       -> Result<Option<Transf<Em>>,Em::Error> {
        let val_sz = val.as_ref().byte_width();
        let mut bw_acc = 0;
        let mut acc = 0;
        for i in 0..self.0.len() {
            if bw_acc > off {
                unimplemented!()
            }
            match self.0[i] {
                MemObj::FreshObj(w) => {
                    if bw_acc+w<=off {
                        bw_acc+=w;
                        continue
                    }
                    if bw_acc==off {
                        self.0[i] = MemObj::ValueObj(val.as_obj());
                        if val_sz != w {
                            self.0.insert(i+1,MemObj::FreshObj(w-val_sz));
                        }
                    } else {
                        self.0[i] = MemObj::FreshObj(off-bw_acc);
                        self.0.insert(i+1,MemObj::ValueObj(val.as_obj()));
                        if val_sz != w+bw_acc-off {
                            self.0.insert(i+2,MemObj::FreshObj(w-val_sz+bw_acc-off));
                        }
                    }
                    let before = Transformation::view(0,acc,inp_sl.clone());
                    let after = Transformation::view(acc,
                                                     inp_sl.size()-acc,
                                                     inp_sl.clone());
                    let res_inp = Transformation::concat(&[before,
                                                           val_inp,
                                                           after]);
                    return Ok(Some(res_inp))
                },
                _ => {}
            }
            match self.0[i] {
                MemObj::ValueObj(ref mut cval) => {
                    let cval_bw = cval.byte_width();
                    let cval_sz = cval.num_elem();
                    if bw_acc+cval_bw<=off {
                        bw_acc+=cval_bw;
                        acc+=cval_sz;
                        continue
                    }
                    if bw_acc==off && cval_bw==val_sz {
                        *cval = val.as_obj();
                        let before = Transformation::view(0,acc,inp_sl.clone());
                        let after = Transformation::view(acc+cval_sz,
                                                         inp_sl.size()-acc-cval_sz,
                                                         inp_sl.clone());
                        let res_inp = Transformation::concat(&[before,
                                                               val_inp,
                                                               after]);
                        return Ok(Some(res_inp))
                    }
                    unimplemented!()
                },
                _ => unimplemented!()
            }
        }
        panic!("Overwrite: {}, {:?}",off,self.0)
    }
    pub fn write<'b,Em : Embed>(&mut self,
                                inp_sl: Transf<Em>,
                                off: OptRef<'b,Offset>,
                                inp_off: Transf<Em>,
                                val: OptRef<'b,V>,
                                val_inp: Transf<Em>,
                                em: &mut Em)
                                -> Result<Option<Transf<Em>>,Em::Error> {
        let (mult,stat_off) = (off.as_ref().0).0;
        match off.as_ref().1 {
            None => self.write_static(inp_sl,stat_off,val,val_inp,em),
            _ => unimplemented!()
        }
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
    pub fn byte_width(&self) -> usize {
        match self {
            &MemObj::FreshObj(w) => w,
            &MemObj::ConstObj(ref dl,_,ref tp,ref tps) => {
                let w = dl.type_size_in_bits(tp,tps);
                if w%8==0 {
                    (w/8) as usize
                } else {
                    (w/8+1) as usize
                }
            },
            &MemObj::ValueObj(ref v) => v.byte_width()
        }
    }
    pub fn as_value<'b,Em : Embed>(obj: OptRef<'b,Self>,
                                   inp: Transf<Em>,
                                   em: &mut Em)
                                -> Result<Option<(OptRef<'b,V>,Transf<Em>)>,Em::Error> {
        match obj {
            OptRef::Ref(&MemObj::FreshObj(_)) |
            OptRef::Owned(MemObj::FreshObj(_)) => Ok(None),
            OptRef::Ref(&MemObj::ConstObj(ref dl,ref c,ref tp,ref tps)) => {
                let res = V::from_const(dl,c,tp,tps,em)?;
                match res {
                    None => Ok(None),
                    Some((x,inp_x)) => Ok(Some((OptRef::Owned(x),inp_x)))
                }
            },
            OptRef::Owned(MemObj::ConstObj(dl,c,tp,tps)) => {
                let res = V::from_const(dl,c,tp,tps,em)?;
                match res {
                    None => Ok(None),
                    Some((x,inp_x)) => Ok(Some((OptRef::Owned(x),inp_x)))
                }
            },
            OptRef::Ref(&MemObj::ValueObj(ref v))
                => Ok(Some((OptRef::Ref(v),inp))),
            OptRef::Owned(MemObj::ValueObj(v))
                => Ok(Some((OptRef::Owned(v),inp)))
        }
    }
}

impl<'a,V : Bytes+FromConst<'a>> Composite for MemSlice<'a,V> {
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
                MemObj::FreshObj(_) => {},
                MemObj::ConstObj(_,_,_,_) => {},
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
                        let w1 = v1.byte_width();
                        let w2 = v2.byte_width();
                        match w1.cmp(&w2) {
                            Ordering::Equal
                                => match V::combine(OptRef::Owned(v1),
                                                    OptRef::Owned(v2),
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
                                    Some((spl2,inp2)) => match V::combine(OptRef::Owned(v1),spl1,
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
                            Ordering::Greater => match V::extract_bytes(OptRef::Ref(&v1),inp_v1.clone(),0,w2,em)? {
                                None => return Ok(None),
                                Some((spl1,inp1)) => match V::extract_bytes(OptRef::Ref(&v1),inp_v1,w2,w1-w2,em)? {
                                    None => return Ok(None),
                                    Some((spl2,inp2)) => match V::combine(spl1,OptRef::Owned(v2),
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
                        let w1 = v1.byte_width();
                        let w2 = v2.byte_width();
                        match w1.cmp(&w2) {
                            Ordering::Equal => match V::combine(OptRef::Owned(v1),
                                                                OptRef::Owned(v2),
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
                                    Some((spl2,inp2)) => match V::combine(OptRef::Owned(v1),spl1,
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
                            Ordering::Greater => match V::extract_bytes(OptRef::Ref(&v1),inp_v1.clone(),0,w2,em)? {
                                None => return Ok(None),
                                Some((spl1,inp1)) => match V::extract_bytes(OptRef::Ref(&v1),inp_v1,w2,w1-w2,em)? {
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

impl<'a,V : Hash> Hash for MemObj<'a,V> {
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

impl<'a,V : Composite> Composite for MemObj<'a,V> {
    fn num_elem(&self) -> usize {
        match self {
            &MemObj::ValueObj(ref v) => v.num_elem(),
            _ => 0
        }
    }
    fn elem_sort<Em : Embed>(&self,pos: usize,em: &mut Em) -> Result<Em::Sort,Em::Error> {
        match self {
            &MemObj::ValueObj(ref v) => v.elem_sort(pos,em),
            _ => panic!("elem_sort called on empty MemObj")
        }
    }
    fn combine<'b, Em, FComb, FL, FR>(
        _: OptRef<'b, Self>, 
        _: OptRef<'b, Self>, 
        _: Transf<Em>, 
        _: Transf<Em>, 
        _: &FComb, 
        _: &FL, 
        _: &FR, 
        _: &mut Em
    ) -> Result<Option<(OptRef<'b, Self>, Transf<Em>)>, Em::Error>
        where
        Em: Embed,
        FComb: Fn(Transf<Em>, Transf<Em>, &mut Em) -> Result<Transf<Em>, Em::Error>,
        FL: Fn(Transf<Em>, &mut Em) -> Result<Transf<Em>, Em::Error>,
        FR: Fn(Transf<Em>, &mut Em) -> Result<Transf<Em>, Em::Error> {
        Ok(None)
    }
}

impl<'b,V> Semantic for MemObj<'b,V>
    where V : Semantic {
    type Meaning = V::Meaning;
    type MeaningCtx = V::MeaningCtx;
    fn meaning(&self,n: usize) -> Self::Meaning {
        match self {
            &MemObj::ValueObj(ref v) => v.meaning(n),
            _ => panic!("meaning called for empty MemObj")
        }
    }
    fn fmt_meaning<F : fmt::Write>(&self,m: &Self::Meaning,fmt: &mut F) -> Result<(),fmt::Error> {
        match self {
            &MemObj::ValueObj(ref v) => v.fmt_meaning(m,fmt),
            _ => panic!("fmt_meaning called for empty MemObj")
        }
    }
    fn first_meaning(&self) -> Option<(Self::MeaningCtx,Self::Meaning)> {
        match self {
            &MemObj::ValueObj(ref v) => v.first_meaning(),
            _ => None
        }
    }
    fn next_meaning(&self,ctx: &mut Self::MeaningCtx,
                    m: &mut Self::Meaning) -> bool {
        match self {
            &MemObj::ValueObj(ref v) => v.next_meaning(ctx,m),
            _ => false
        }
    }
}

impl<'b,V : Semantic+Bytes+FromConst<'b>> Semantic for MemSlice<'b,V> {
    type Meaning = VecMeaning<V::Meaning>;
    type MeaningCtx = V::MeaningCtx;
    fn meaning(&self,n: usize) -> Self::Meaning {
        self.0.meaning(n)
    }
    fn fmt_meaning<F : fmt::Write>(&self,m: &Self::Meaning,fmt: &mut F) -> Result<(),fmt::Error> {
        self.0.fmt_meaning(m,fmt)
    }
    fn first_meaning(&self) -> Option<(Self::MeaningCtx,Self::Meaning)> {
        self.0.first_meaning()
    }
    fn next_meaning(&self,ctx: &mut Self::MeaningCtx,
                    m: &mut Self::Meaning) -> bool {
        self.0.next_meaning(ctx,m)
    }
}
