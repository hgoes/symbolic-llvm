use smtrs::composite::*;
use smtrs::composite::vec::*;
use smtrs::composite::singleton::*;
use smtrs::embed::{Embed};
use smtrs::expr;
use std::cmp::{Ordering,max};
use llvm_ir::datalayout::DataLayout;
use llvm_ir::types::{Type as LLVMType};
use llvm_ir;
use std::collections::HashMap;
use std::hash::{Hash,Hasher};
use super::pointer::Offset;
use std::fmt::Debug;
use std::fmt;
use std::mem::swap;
use std::marker::PhantomData;

pub trait Bytes<'a>: Composite<'a> {
    fn byte_width(&self) -> usize;
    fn extract_bytes<Em: Embed,From,P: Path<'a,Em,From,To=Self>>(
        &P,&From,&[Em::Expr],
        usize,usize,
        &mut Vec<Em::Expr>,
        &mut Em
    ) -> Result<Option<Self>,Em::Error>
        where Self: 'a {
        Ok(None)
    }
    fn concat_bytes<Em: Embed,
                    From1,P1: Path<'a,Em,From1,To=Self>,
                    From2,P2: Path<'a,Em,From2,To=Self>>(
        &P1,&From1,&[Em::Expr],
        &P2,&From2,&[Em::Expr],
        &mut Vec<Em::Expr>,
        &mut Em
    ) -> Result<Option<Self>,Em::Error>
        where Self: 'a {
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

#[derive(Clone)]
pub struct MemObjValue;

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub struct MemSlice<'a,V>(pub CompVec<MemObj<'a,V>>);

#[derive(Clone)]
pub struct MemObjs;

pub trait FromConst<'a>: Composite<'a> {
    fn from_const<Em: Embed>(&'a DataLayout,
                             &'a llvm_ir::Constant,
                             &'a LLVMType,
                             &'a HashMap<String,LLVMType>,
                             &mut Vec<Em::Expr>,
                             &mut Em)
                             -> Result<Option<Self>,Em::Error>;
}

impl<'a,V: Debug> Debug for MemObj<'a,V> {
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

impl<'a,V: 'a+Composite<'a>> MemSlice<'a,V> {
    pub fn objects() -> MemObjs {
        MemObjs
    }
    pub fn alloca<Em: Embed>(sz: usize,
                             res: &mut Vec<Em::Expr>,
                             em: &mut Em) -> Result<Self,Em::Error> {
        let mut vec0 = CompVec::new(res,em)?;
        CompVec::push(&Id::new(),&mut vec0,res,
                      MemObj::FreshObj(sz),
                      &mut Vec::new(),
                      em)?;
        Ok(MemSlice(vec0))
    }
    pub fn realloc<Em: Embed,From,P: Path<'a,Em,From,To=Self>>(
        path: P,
        from: &mut From,
        arr:  &mut Vec<Em::Expr>,
        sz:   usize,
        em:   &mut Em
    ) -> Result<(),Em::Error>
        where V: Bytes<'a>+FromConst<'a> {
        let csz = path.get(from).byte_width();
        if sz==csz {
            return Ok(())
        }
        if sz < csz {
            panic!("Making slices smaller not yet supported")
        }
        CompVec::push(&then(path,MemObjs),
                      from,arr,
                      MemObj::FreshObj(sz-csz),
                      &mut Vec::new(),em)
    }
    pub fn is_free(&self) -> bool {
        false
    }
    pub fn byte_width(&self) -> usize
        where V: Bytes<'a>+FromConst<'a> {
        let mut bw = 0;
        for i in 0..self.0.len() {
            bw += self.0[i].byte_width()
        }
        bw
    }
    pub fn read_static<Em: Embed,From,P: Path<'a,Em,From,To=Self>>(
        path: &P,
        from: &From,
        src:  &[Em::Expr],
        off: usize,
        len: usize,
        res: &mut Vec<Em::Expr>,
        em: &mut Em
    )  -> Result<Option<V>,Em::Error>
        where V: Bytes<'a>+FromConst<'a> {
        //println!("Reading at {} with len {} from {:#?}",off,len,sl.as_ref());
        let mut buf = Vec::new();
        let mut buf2 = Vec::new();
        let mut acc = 0;
        for n in 0..path.get(from).0.len() {
            let obj_path = path.clone()
                .then(Self::objects())
                .then(CompVecP(n));
            let bw = obj_path.get(from).byte_width();
            if off<acc+bw {
                if off==acc && bw==len {
                    return MemObj::as_value(&obj_path,from,src,res,em)
                }
                if off-acc+len<=bw {
                    return match MemObj::as_value(&obj_path,from,src,
                                                  &mut buf,em)? {
                        None => panic!("Reading from uninitialized memory at {}, previous element {}",off,acc),//Ok(None),
                        Some(sobj) => {
                            V::extract_bytes(&Id::new(),&sobj,
                                             &buf[..],
                                             off-acc,len,
                                             res,em)
                        }
                    }
                }
                let start = {
                    match MemObj::as_value(&obj_path,from,src,&mut buf,em)? {
                        None => panic!("Reading from uninitialized memory"),//return Ok(None),
                        Some(val0) => if off==acc {
                            val0
                        } else {
                            match V::extract_bytes(&Id::new(),&val0,
                                                   &buf[..],
                                                   off-acc,bw+acc-off,
                                                   &mut buf2,em)? {
                                None => panic!("Failed to extract bytes"),//return Ok(None),
                                Some(res) => {
                                    swap(&mut buf,&mut buf2);
                                    buf2.clear();
                                    res
                                }
                            }
                        }
                    }
                };
                acc+=bw;
                let rest = len+acc-off;
                let mut cur = start;
                for m in n..path.get(from).0.len() {
                    let obj_path = path.clone()
                        .then(Self::objects())
                        .then(CompVecP(m));
                    let bw = obj_path.get(from).byte_width();
                    let cpos = buf.len();
                    let val = match MemObj::as_value(&obj_path,from,src,
                                                     &mut buf,em)? {
                        None => panic!("Reading from uninitialized memory"),//return Ok(None),
                        Some(res) => res
                    };
                    if rest<bw {
                        let rval = match V::extract_bytes(&Id::new(),
                                                          &val,
                                                          &buf[cpos..],
                                                          0,rest,
                                                          &mut buf2,em)? {
                            None => panic!("Reading from uninitialized memory"),//return Ok(None),
                            Some(res) => res
                        };
                        return V::concat_bytes(&Id::new(),
                                               &cur,&buf[0..cpos],
                                               &Id::new(),
                                               &rval,&buf2,
                                               res,em)
                    }
                    let ncur = match V::concat_bytes(
                        &Id::new(),&cur,&buf[0..cpos],
                        &Id::new(),&val,&buf[cpos..],
                        &mut buf2,em)? {
                        None => panic!("Cannot concat bytes"),//return Ok(None),
                        Some(res) => res
                    };
                    buf.clear();
                    swap(&mut buf,&mut buf2);
                    cur = ncur;
                    acc+=bw;
                }
                return panic!("Overread")//Ok(None)
            }
            acc+=bw;
        }
        panic!("Overread") //Ok(None)
    }
    pub fn read<Em: Embed,From,
                P: Path<'a,Em,From,To=Self>,
                FromOff,
                POff: Path<'a,Em,FromOff,To=Offset>>(
        path: &P,
        from: &From,
        src:  &[Em::Expr],
        path_off: &POff,
        from_off: &FromOff,
        src_off:  &[Em::Expr],
        len: usize,
        res: &mut Vec<Em::Expr>,
        em: &mut Em
    ) -> Result<Option<V>,Em::Error>
        where V: Bytes<'a>+FromConst<'a> {
        let off = path_off.get(from_off);
        let (mult,stat_off) = (off.0).0;
        match off.1 {
            None => Self::read_static(path,from,src,
                                      stat_off,len,res,em),
            Some(_) => Ok(None)
        }
    }
    /*pub fn read<Em: Embed,P: Path<'a,Em,To=Self>>(
        path: &P,
        from: &P::From,
        src:  &[Em::Expr],
        off: OptRef<'b,Offset>,
                               inp_off: Transf<Em>,
                               len: usize,
                               em: &mut Em)
                               -> Result<Option<(OptRef<'b,V>,Transf<Em>)>,Em::Error> {
        let (mult,stat_off) = (off.as_ref().0).0;
        match off.as_ref().1 {
            None => Self::read_static(sl,inp_sl,stat_off,len,em),
            Some(ref singleton) => {
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
                    let (nval,inp_nval) = match ite(rval,cval,cond,inp_rval,inp_cval,em)? {
                        None => return Ok(None),
                        Some(r) => r
                    };
                    cval = nval;
                    inp_cval = inp_nval;
                }
                Ok(Some((OptRef::Owned(cval.as_obj()),inp_cval)))
            }
        }
    }*/
    pub fn write_static<From,P: Path<'a,Em,From,To=Self>,
                        Em: Embed>(
        path: P,
        from: &mut From,
        inp:  &mut Vec<Em::Expr>,
        off: usize,
        val: V,
        val_inp: &mut Vec<Em::Expr>,
        cond: Option<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error>
        where V: Bytes<'a>+FromConst<'a> {
        let rpath = then(path,MemObjs);
        let val_bw = val.byte_width();
        let mut bw_acc = 0;
        for i in 0..rpath.get(from).len() {
            let el_path = then(rpath.clone(),
                               CompVecP(i));
            let bw = el_path.get(from).byte_width();
            if bw_acc > off {
                unimplemented!()
            }
            if bw_acc+bw<=off {
                bw_acc+=bw;
                continue
            }
            let mut old_val_inp = Vec::new();
            let old_val = MemObj::as_value(&el_path,from,&inp[..],
                                           &mut old_val_inp,em)?;
            match old_val {
                None => {
                    // Current object is fresh
                    el_path.set(from,inp,
                                MemObj::ValueObj(val),
                                val_inp,em)?;
                    if bw_acc<off {
                        CompVec::insert(&rpath,from,inp,i,
                                        MemObj::FreshObj(off-bw_acc),
                                        &mut Vec::new(),em)?;
                        match (off-bw_acc+val_bw).cmp(&bw) {
                            Ordering::Less => {
                                CompVec::insert(&rpath,from,inp,i+2,
                                                MemObj::FreshObj(bw+bw_acc-off-val_bw),
                                                &mut Vec::new(),em)?;
                            },
                            Ordering::Equal => {},
                            Ordering::Greater => unimplemented!()
                        }
                    } else { //bw_acc==off
                        match val_bw.cmp(&bw) {
                            Ordering::Less => {
                                CompVec::insert(&rpath,from,inp,i+1,
                                                MemObj::FreshObj(bw+bw_acc-off-val_bw),
                                                &mut Vec::new(),em)?;
                            },
                            Ordering::Equal => {},
                            Ordering::Greater => unimplemented!()
                        }
                    }
                },
                Some(rold_val) => {
                    if val_bw!=bw {
                        unimplemented!()
                    }
                    match cond {
                        None => {
                            el_path.set(from,inp,
                                        MemObj::ValueObj(val),
                                        val_inp,em)?;
                        },
                        Some(rcond) => {
                            let mut nval_inp = Vec::new();
                            let nval = ite(&rcond,
                                           &Id,&val,&val_inp[..],
                                           &Id,&rold_val,&old_val_inp[..],
                                           &mut nval_inp,em)?
                            .expect("Failed to merge when writing memory");
                            el_path.set(from,inp,
                                        MemObj::ValueObj(nval),
                                        &mut nval_inp,em)?;
                        }
                    }
                }
            }
            return Ok(())
        }
        panic!("Overwrite: {}",off)
    }
    pub fn write<From,P: Path<'a,Em,From,To=Self>,
                 FromOff,POff: Path<'a,Em,FromOff,To=Offset>,
                 Em: Embed>(
        path: P,
        from: &mut From,
        inp: &mut Vec<Em::Expr>,
        off: &POff,
        from_off: &FromOff,
        inp_off: &[Em::Expr],
        val: V,
        val_inp: &mut Vec<Em::Expr>,
        cond: Option<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error>
        where V: Bytes<'a>+FromConst<'a> {
        let &(Data((mult,stat_off)),ref dyn) = off.get(from_off);
        match dyn {
            &None => Self::write_static(path,from,inp,
                                        stat_off,val,val_inp,cond,em),
            _ => unimplemented!()
        }
    }        
}

impl<'a,V: HasSorts> HasSorts for MemObj<'a,V> {
    fn num_elem(&self) -> usize {
        match self {
            &MemObj::FreshObj(_) => 0,
            &MemObj::ConstObj(_,_,_,_) => 0,
            &MemObj::ValueObj(ref v) => v.num_elem()
        }
    }
    fn elem_sort<Em: Embed>(&self,n: usize,em: &mut Em)
                            -> Result<Em::Sort,Em::Error> {
        match self {
            &MemObj::ValueObj(ref v) => v.elem_sort(n,em),
            _ => unreachable!()
        }
    }
}

impl<'a,V: 'a+Bytes<'a>+FromConst<'a>> MemObj<'a,V> {
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
    pub fn as_value<Em: Embed,From,P: Path<'a,Em,From,To=Self>>(
        path: &P,
        from: &From,
        arr:  &[Em::Expr],
        res:  &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<Option<V>,Em::Error> {
        let obj = path.get(from);
        match obj {
            &MemObj::FreshObj(_) => Ok(None),
            &MemObj::ConstObj(ref dl,ref c,ref tp,ref tps) => {
                let res = V::from_const(dl,c,tp,tps,res,em)?;
                match res {
                    None => Ok(None),
                    Some(x) => Ok(Some(x))
                }
            },
            &MemObj::ValueObj(ref v) => {
                path.read_into(from,0,v.num_elem(),arr,res,em)?;
                Ok(Some(v.clone()))
            }
        }
    }
}

impl<'a,V : HasSorts> HasSorts for MemSlice<'a,V> {
    fn num_elem(&self) -> usize {
        self.0.num_elem()
    }
    fn elem_sort<Em : Embed>(&self,pos: usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        self.0.elem_sort(pos,em)
    }
}

impl<'a,V: Bytes<'a>+FromConst<'a>> Composite<'a> for MemSlice<'a,V> {
    fn combine<Em,FromL,PL,FromR,PR,FComb,FL,FR>(
        pl: &PL,froml: &FromL,arrl: &[Em::Expr],
        pr: &PR,fromr: &FromR,arrr: &[Em::Expr],
        comb: &FComb,only_l: &FL,only_r: &FR,
        res: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<Option<Self>,Em::Error>
        where
        Self: 'a,
        Em: Embed,
        PL: Path<'a,Em,FromL,To=Self>,
        PR: Path<'a,Em,FromR,To=Self>,
        FComb: Fn(Em::Expr,Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
        FL: Fn(Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
        FR: Fn(Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error> {

        let lhs = pl.get(froml);
        let rhs = pr.get(fromr);
        
        let mut pos_x = 0;
        let mut pos_y = 0;

        let mut cur_x: Option<MemObj<V>> = None;
        let mut buf_x: Vec<Em::Expr> = Vec::new();
        let mut cur_y: Option<MemObj<V>> = None;
        let mut buf_y: Vec<Em::Expr> = Vec::new();

        let mut outp = CompVec::new(res,em)?;
        
        loop {
            let x = match cur_x.take() {
                None => {
                    if pos_x >= lhs.0.len() {
                        match cur_y.take() {
                            None => {},
                            Some(y) => {
                                for e in buf_y.iter_mut() {
                                    *e = only_r(e.clone(),em)?;
                                }
                                CompVec::push(&Id::new(),&mut outp,
                                              res,y,&mut buf_y,em)?;
                                buf_y.clear();
                            }
                        }
                        for i in pos_y..rhs.0.len() {
                            let cpos = res.len();
                            let path_el = then(then(pr.clone(),
                                                    MemObjs),
                                               CompVecP(i));
                            let el = path_el.get(fromr);
                            path_el.read_into(fromr,0,el.num_elem(),arrr,res,em)?;
                            for i in cpos..res.len() {
                                res[i] = only_r(res[i].clone(),em)?;
                            }
                        }
                        break
                    }
                    let path_el = pl.clone()
                        .then(Self::objects())
                        .then(CompVecP(pos_x));
                    let el = path_el.get(froml);
                    let len = el.num_elem();
                    path_el.read_into(froml,0,len,arrl,&mut buf_x,em)?;
                    pos_x+=1;
                    el.clone()
                },
                Some(el) => el
            };
            let y = match cur_y.take() {
                None => {
                    if pos_y >= rhs.0.len() {
                        CompVec::push(&Id::new(),&mut outp,
                                      res,x,&mut buf_x,em)?;
                        buf_x.clear();
                        for i in pos_x..lhs.0.len() {
                            let cpos = res.len();
                            let path_el = pl.clone()
                                .then(Self::objects())
                                .then(CompVecP(i));
                            let el = path_el.get(froml);
                            path_el.read_into(froml,0,el.num_elem(),arrl,res,em)?;
                            for i in cpos..res.len() {
                                res[i] = only_l(res[i].clone(),em)?;
                            }
                        }
                        break
                    }
                    let path_el = pr.clone()
                        .then(Self::objects())
                        .then(CompVecP(pos_y));
                    let el = path_el.get(fromr);
                    let len = el.num_elem();
                    path_el.read_into(fromr,0,len,arrr,&mut buf_y,em)?;
                    pos_y+=1;
                    el.clone()
                },
                Some(el) => el
            };
            match x {
                MemObj::FreshObj(w1) => match y {
                    MemObj::FreshObj(w2) => match w1.cmp(&w2) {
                        Ordering::Equal => {
                            CompVec::push(&Id::new(),&mut outp,
                                          res,x,&mut buf_x,em)?;
                        },
                        Ordering::Less => {
                            CompVec::push(&Id::new(),&mut outp,
                                          res,x,&mut buf_x,em)?;
                            cur_y = Some(MemObj::FreshObj(w2-w1));
                        },
                        Ordering::Greater => {
                            CompVec::push(&Id::new(),&mut outp,
                                          res,y,&mut buf_y,em)?;
                            cur_x = Some(MemObj::FreshObj(w1-w2));
                        }
                    },
                    MemObj::ConstObj(_,_,_,_) => return Ok(None),
                    MemObj::ValueObj(ref v2) => {
                        let w2 = v2.byte_width();
                        match w1.cmp(&w2) {
                            Ordering::Equal => {
                                CompVec::push(&Id::new(),&mut outp,
                                              res,y.clone(),&mut buf_y,em)?;
                                buf_y.clear();
                            },
                            Ordering::Less => match V::extract_bytes(&Id::new(),&v2,&buf_y[..],0,w1,
                                                                     &mut buf_x,em)? {
                                None => return Ok(None),
                                Some(spl1) => {
                                    // buf_x contains spl1
                                    let len_spl1 = buf_x.len();
                                    match V::extract_bytes(&Id::new(),&v2,&buf_y[..],w1,w2-w1,
                                                           &mut buf_x,em)? {
                                        None => return Ok(None),
                                        Some(spl2) => {
                                            // buf_x contains spl1+spl2
                                            CompVec::push(&Id::new(),&mut outp,
                                                          res,MemObj::ValueObj(spl1),
                                                          &mut buf_x,em)?;
                                            buf_x.drain(0..len_spl1);
                                            // buf_x contains spl2
                                            cur_y = Some(MemObj::ValueObj(spl2));
                                            swap(&mut buf_x,&mut buf_y);
                                        }
                                    }
                                }
                            },
                            Ordering::Greater => {
                                CompVec::push(&Id::new(),&mut outp,
                                              res,y.clone(),&mut buf_y,em)?;
                                buf_y.clear();
                                cur_x = Some(MemObj::FreshObj(w1-w2));
                            }
                        }
                    }
                },
                MemObj::ConstObj(dl,c,tp,tps) => match y {
                    MemObj::FreshObj(_) => return Ok(None),
                    MemObj::ConstObj(_,nc,ntp,_) => if c==nc {
                        CompVec::push(&Id::new(),&mut outp,
                                      res,x.clone(),&mut buf_x,em)?;
                    } else {
                        cur_x = match V::from_const(dl,c,tp,tps,
                                                    &mut buf_x,em)? {
                            None => return Ok(None),
                            Some(r) => Some(MemObj::ValueObj(r))
                        };
                        cur_y = match V::from_const(dl,nc,ntp,tps,
                                                    &mut buf_y,em)? {
                            None => return Ok(None),
                            Some(r) => Some(MemObj::ValueObj(r))
                        };
                    },
                    MemObj::ValueObj(v2) => {
                        cur_x = match V::from_const(dl,c,tp,tps,
                                                    &mut buf_x,em)? {
                            None => return Ok(None),
                            Some(r) => Some(MemObj::ValueObj(r))
                        };
                    }
                },
                MemObj::ValueObj(ref v1) => match y {
                    MemObj::FreshObj(w2) => {
                        let w1 = v1.byte_width();
                        match w2.cmp(&w1) {
                            Ordering::Equal => {
                                for i in 0..buf_x.len() {
                                    buf_x[i] = only_l(buf_x[i].clone(),em)?;
                                }
                                CompVec::push(&Id::new(),&mut outp,
                                              res,x.clone(),&mut buf_x,em)?;
                                buf_x.clear();
                            },
                            Ordering::Less => match V::extract_bytes(&Id::new(),&v1,&buf_x[..],0,w2,
                                                                     &mut buf_y,em)? {
                                None => return Ok(None),
                                Some(spl1) => {
                                    // buf_y contains spl1
                                    let len_spl1 = buf_y.len();
                                    match V::extract_bytes(&Id::new(),&v1,&buf_x[..],w2,w1-w2,
                                                           &mut buf_y,em)? {
                                        None => return Ok(None),
                                        Some(spl2) => {
                                            // buf_y contains spl1+spl2
                                            CompVec::push(&Id::new(),&mut outp,
                                                          res,MemObj::ValueObj(spl1),
                                                          &mut buf_y,em)?;
                                            buf_y.drain(0..len_spl1);
                                            // buf_x contains spl2
                                            cur_x = Some(MemObj::ValueObj(spl2));
                                            swap(&mut buf_x,&mut buf_y);
                                        }
                                    }
                                }
                            },
                            Ordering::Greater => {
                                for i in 0..buf_x.len() {
                                    buf_x[i] = only_l(buf_x[i].clone(),em)?;
                                }
                                CompVec::push(&Id::new(),&mut outp,
                                              res,x.clone(),&mut buf_x,em)?;
                                buf_x.clear();
                                cur_y = Some(MemObj::FreshObj(w2-w1));
                            }
                        }
                    },
                    _ => {
                        let cpos = buf_x.len();
                        match MemObj::as_value(&Id::new(),
                                               &y,&buf_y[..],
                                               &mut buf_x,em)? {
                            None => return Ok(None),
                            Some(v2) => {
                                // buf_x contains y as value
                                let w1 = v1.byte_width();
                                let w2 = v2.byte_width();
                                buf_y.clear();
                                match w1.cmp(&w2) {
                                    Ordering::Equal => match V::combine(
                                        &Id::new(),v1,&buf_x[..cpos],
                                        &Id::new(),&v2,&buf_x[cpos..],
                                        comb,only_l,only_r,&mut buf_y,em)? {
                                        None => return Ok(None),
                                        Some(nv) => {
                                            CompVec::push(&Id::new(),&mut outp,
                                                          res,
                                                          MemObj::ValueObj(nv),
                                                          &mut buf_y,em)?;
                                            buf_x.clear();
                                            buf_y.clear();
                                        }
                                    },
                                    Ordering::Less => {
                                        match V::extract_bytes(
                                            &Id::new(),&v2,&buf_x[cpos..],
                                            0,w1,&mut buf_y,em)? {
                                            None => return Ok(None),
                                            Some(spl1) => {
                                                let cpos2 = buf_y.len();
                                                match V::extract_bytes(
                                                    &Id::new(),&v2,&buf_x[cpos..],
                                                    w1,w2-w1,&mut buf_y,em)? {
                                                    None => return Ok(None),
                                                    Some(spl2) => {
                                                        let mut tmp = Vec::new();
                                                        match V::combine(
                                                            &Id::new(),
                                                            v1,&buf_x[..cpos],
                                                            &Id::new(),
                                                            &spl1,&buf_y[..cpos2],
                                                            comb,only_l,only_r,
                                                            &mut tmp,em)? {
                                                            None => return Ok(None),
                                                            Some(nv) => {
                                                                CompVec::push(&Id::new(),
                                                                              &mut outp,
                                                                              res,
                                                                              MemObj::ValueObj(nv),
                                                                              &mut tmp,em)?;
                                                                buf_x.clear();
                                                                buf_y.drain(..cpos2);
                                                                cur_y = Some(MemObj::ValueObj(spl2));
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    },
                                    Ordering::Greater => {
                                        match V::extract_bytes(
                                            &Id::new(),v1,&buf_x[..cpos],
                                            0,w2,&mut buf_y,em)? {
                                            None => return Ok(None),
                                            Some(spl1) => {
                                                let cpos2 = buf_y.len();
                                                match V::extract_bytes(
                                                    &Id::new(),v1,&buf_x[..cpos],
                                                    w2,w1-w2,&mut buf_y,em)? {
                                                    None => return Ok(None),
                                                    Some(spl2) => {
                                                        let mut tmp = Vec::new();
                                                        match V::combine(
                                                            &Id::new(),
                                                            &v2,&buf_x[cpos..],
                                                            &Id::new(),
                                                            &spl1,&buf_y[..cpos2],
                                                            comb,only_l,only_r,
                                                            &mut tmp,em)? {
                                                            None => return Ok(None),
                                                            Some(nv) => {
                                                                CompVec::push(&Id::new(),
                                                                              &mut outp,
                                                                              res,
                                                                              MemObj::ValueObj(nv),
                                                                              &mut tmp,em)?;
                                                                buf_x.clear();
                                                                buf_y.drain(..cpos2);
                                                                cur_y = Some(MemObj::ValueObj(spl2));
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
                    }
                }
            }
        }
        Ok(Some(MemSlice(outp)))
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

/*impl<'a,V : HasSorts> HasSorts for MemObj<'a,V> {
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
}

impl<'a,V : Composite> Composite for MemObj<'a,V> {
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
}*/

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

impl<'b,V: Semantic+Bytes<'b>+FromConst<'b>> Semantic for MemSlice<'b,V> {
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

impl<'a,V: 'a> SimplePathEl<'a,MemSlice<'a,V>> for MemObjs {
    type To = CompVec<MemObj<'a,V>>;
    fn get<'c>(&self,from: &'c MemSlice<'a,V>) -> &'c Self::To where 'a: 'c {
        &from.0
    }
    fn get_mut<'c>(&self,from: &'c mut MemSlice<'a,V>)
                   -> &'c mut Self::To where 'a: 'c {
        &mut from.0
    }
}

impl<'a,Em: Embed,V: 'a> PathEl<'a,Em,MemSlice<'a,V>> for MemObjs {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=MemSlice<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        prev.read(prev_from,pos,arr,em)
    }
    fn read_slice<'c,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=MemSlice<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        len: usize,
        arr: &'c [Em::Expr])
        -> Option<&'c [Em::Expr]> {
        prev.read_slice(prev_from,pos,len,arr)
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=MemSlice<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        e: Em::Expr,
        arr: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        prev.write(prev_from,pos,e,arr,em)
    }
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=MemSlice<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &mut PrevFrom,
        pos: usize,
        old_len: usize,
        src: &mut Vec<Em::Expr>,
        trg: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        prev.write_slice(prev_from,pos,old_len,src,trg,em)
    }
}

impl<'a,V: 'a> SimplePathEl<'a,MemObj<'a,V>> for MemObjValue {
    type To = V;
    fn get<'c>(&self,from: &'c MemObj<'a,V>) -> &'c Self::To where 'a: 'c {
        match from {
            &MemObj::ValueObj(ref v) => v,
            _ => panic!("Value path for non-value object")
        }
    }
    fn get_mut<'c>(&self,from: &'c mut MemObj<'a,V>)
                   -> &'c mut Self::To where 'a: 'c {
        match from {
            &mut MemObj::ValueObj(ref mut v) => v,
            _ => panic!("Value path for non-value object")
        }
    }
}

impl<'a,Em: Embed,V: 'a> PathEl<'a,Em,MemObj<'a,V>> for MemObjValue {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=MemObj<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        prev.read(prev_from,pos,arr,em)
    }
    fn read_slice<'c,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=MemObj<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        len: usize,
        arr: &'c [Em::Expr])
        -> Option<&'c [Em::Expr]> {
        prev.read_slice(prev_from,pos,len,arr)
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=MemObj<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        e: Em::Expr,
        arr: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        prev.write(prev_from,pos,e,arr,em)
    }
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=MemObj<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &mut PrevFrom,
        pos: usize,
        old_len: usize,
        src: &mut Vec<Em::Expr>,
        trg: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        prev.write_slice(prev_from,pos,old_len,src,trg,em)
    }
}
