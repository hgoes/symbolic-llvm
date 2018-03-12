use smtrs::composite::*;
use smtrs::composite::map::*;
use smtrs::composite::stack::*;
use smtrs::composite::choice::*;
use smtrs::composite::singleton::*;
use smtrs::composite::tuple::*;
use smtrs::composite::vec::*;
use smtrs::embed::{Embed,DeriveConst,DeriveValues};
use super::mem::{Bytes,FromConst};
use super::frame::*;
use super::{InstructionRef};
use std::marker::PhantomData;
use num_bigint::{BigInt,BigUint};
use std::ops::Range;
use std::cmp::Ordering;
use std::hash::{Hash,Hasher};
use std::fmt;
use std::fmt::Debug;

pub type CallId<'a> = (Option<InstructionRef<'a>>,&'a String);

pub type CallStack<'a,V> = Assoc<CallId<'a>,
                                 BitVecVectorStack<(CallFrame<'a,V>,Frame<'a,V>)>>;
pub type Stack<'a,V> = Assoc<InstructionRef<'a>,
                             BitVecVectorStack<Frame<'a,V>>>;
pub type StackTop<'a> = Choice<Data<Option<ContextId<'a>>>>;

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub struct Thread<'a,V> {
    call_stack: CallStack<'a,V>,
    stack: Stack<'a,V>,
    stack_top: StackTop<'a>,
    ret: Option<V>
}

impl<'a,V> Thread<'a,V> {
    pub fn construct<Em,FCs,FSt,FTop,FRet>(
        cs: FCs,
        st: FSt,
        top: FTop,
        ret: FRet,
        res: &mut Vec<Em::Expr>,
        em: &mut Em
    ) -> Result<Self,Em::Error>
        where Em: Embed,
              FCs: FnOnce(&mut Vec<Em::Expr>,&mut Em)
                          -> Result<CallStack<'a,V>,Em::Error>,
              FSt: FnOnce(&mut Vec<Em::Expr>,&mut Em)
                          -> Result<Stack<'a,V>,Em::Error>,
              FTop: FnOnce(&mut Vec<Em::Expr>,&mut Em)
                          -> Result<StackTop<'a>,Em::Error>,
              FRet: FnOnce(&mut Vec<Em::Expr>,&mut Em)
                           -> Result<Option<V>,Em::Error> {
        let callstack = cs(res,em)?;
        let stack = st(res,em)?;
        let rtop = top(res,em)?;
        let rret = ret(res,em)?;
        Ok(Thread { call_stack: callstack,
                    stack: stack,
                    stack_top: rtop,
                    ret: rret })
    }
    pub fn call_stack() -> CallStackPath {
        CallStackPath
    }
    pub fn stack() -> StackPath {
        StackPath
    }
    pub fn stack_top() -> StackTopPath {
        StackTopPath
    }
    pub fn ret() -> RetPath {
        RetPath
    }
}

/*
pub fn get_top_call_frame<'a,'b,V,Em>(cfs: OptRef<'a,CallStack<'b,V>>,
                                      cfs_inp: Transf<Em>,
                                      cf_id: &CallId<'b>,
                                      exprs: &[Em::Expr],
                                      em: &mut Em)
                                      -> Result<Option<(OptRef<'a,CallFrame<'b,V>>,Transf<Em>)>,Em::Error>
    where V : Bytes+FromConst<'b>+Clone,Em : DeriveConst {
    match assoc_get(cfs,cfs_inp,cf_id)? {
        None => Ok(None),
        Some((st,st_inp)) => match bv_vec_stack_get_top(st,st_inp,exprs,em)? {
            None => Ok(None),
            Some((cf,cf_inp)) => Ok(Some(fst(cf,cf_inp)?))
        }
    }
}

pub fn call_frame_activation<'a,'b,'c,Em>(top: OptRef<'a,StackTop<'b>>,
                                          top_inp: Transf<Em>,
                                          cf_id: &CallId<'b>,
                                          _: &mut Em)
                                          -> Result<Transf<Em>,Em::Error>
    where Em : Embed {
    let mut res = Vec::new();
    for (ref el,ref cond,_) in top.as_ref().choices(top_inp) {
        let same_cf = match el.0 {
            None => false,
            Some(ref fr_id) => match fr_id {
                &ContextId::Call(ref id) => *id==*cf_id,
                &ContextId::Stack(ref id,_) => *id==*cf_id
            }
        };
        if same_cf {
            res.push(cond.clone());
        }
    }
    let rview = Transformation::concat(&res[..]);
    let fcond = |exprs:&[Em::Expr],res:&mut Vec<Em::Expr>,em:&mut Em| {
        res.push(em.or(exprs.to_vec())?);
        Ok(())
    };
    let cond  = Transformation::map(1,Box::new(fcond),rview);
    Ok(cond)
}
                                                        

fn thread_get_call_stack<'a,'b,V,Em>(thr: OptRef<'a,Thread<'b,V>>,
                                     thr_inp: Transf<Em>)
                                     -> (OptRef<'a,Assoc<CallId<'b>,
                                                         BitVecVectorStack<(CallFrame<'b,V>,Frame<'b,V>)>>>,
                                         Transf<Em>)
    where V : Bytes+FromConst<'b>+Clone,Em : Embed {
    let sz = thr.as_ref().call_stack.num_elem();
    let cs = match thr {
        OptRef::Ref(ref rthr) => OptRef::Ref(&rthr.call_stack),
        OptRef::Owned(rthr) => OptRef::Owned(rthr.call_stack)
    };
    let cs_inp = Transformation::view(0,sz,thr_inp);
    (cs,cs_inp)
}

fn thread_get_stack<'a,'b,V,Em>(thr: OptRef<'a,Thread<'b,V>>,
                                thr_inp: Transf<Em>)
                                -> (OptRef<'a,Assoc<InstructionRef<'b>,
                                                    BitVecVectorStack<Frame<'b,V>>>>,
                                    Transf<Em>)
    where V : Bytes+FromConst<'b>+Clone,Em : Embed {
    let off = thr.as_ref().call_stack.num_elem();
    let sz = thr.as_ref().stack.num_elem();
    let st = match thr {
        OptRef::Ref(ref rthr) => OptRef::Ref(&rthr.stack),
        OptRef::Owned(rthr) => OptRef::Owned(rthr.stack)
    };
    let st_inp = Transformation::view(off,sz,thr_inp);
    (st,st_inp)
}

fn thread_get_stack_top<'a,'b,V,Em>(thr: OptRef<'a,Thread<'b,V>>,
                                    thr_inp: Transf<Em>)
                                    -> (OptRef<'a,Choice<Data<Option<ContextId<'b>>>>>,
                                        Transf<Em>)
    where V : Bytes+FromConst<'b>+Clone,Em : Embed {
    let off = thr.as_ref().call_stack.num_elem() +
        thr.as_ref().stack.num_elem();
    let sz = thr.as_ref().stack_top.num_elem();
    let top = match thr {
        OptRef::Ref(ref rthr) => OptRef::Ref(&rthr.stack_top),
        OptRef::Owned(rthr) => OptRef::Owned(rthr.stack_top)
    };
    let top_inp = Transformation::view(off,sz,thr_inp);
    (top,top_inp)
}

pub fn thread_get_frame<'a,'b,V,Em>(thr: OptRef<'a,Thread<'b,V>>,
                                    inp_thr: Transf<Em>,
                                    fr_id: &FrameId<'b>,
                                    idx: Transf<Em>,
                                    exprs: &[Em::Expr],
                                    em: &mut Em)
                                    -> Result<Option<(OptRef<'a,Frame<'b,V>>,Transf<Em>)>,Em::Error>
    where V : Bytes+FromConst<'b>+Clone,Em : DeriveConst {

    match fr_id {
        &FrameId::Call(ref cs_id) => {
            let (css,css_inp) = thread_get_call_stack(thr,inp_thr);
            match assoc_get(css,css_inp,cs_id)? {
                None => Ok(None),
                Some((cs,cs_inp)) => match bv_vec_stack_get(cs,cs_inp,idx,exprs,em)? {
                    None => Ok(None),
                    Some((el,el_inp)) => Ok(Some(snd(el,el_inp)?))
                }
            }
        },
        &FrameId::Stack(ref st_id) => {
            let (sts,sts_inp) = thread_get_stack(thr,inp_thr);
            match assoc_get(sts,sts_inp,st_id)? {
                None => Ok(None),
                Some((st,st_inp)) => bv_vec_stack_get(st,st_inp,idx,exprs,em)
            }
        },
    }
}

pub fn thread<'a,'b,'c,V,Em>(cs: OptRef<'a,CallStack<'b,V>>,
                             inp_cs: Transf<Em>,
                             st: OptRef<'a,Stack<'b,V>>,
                             inp_st: Transf<Em>,
                             top: OptRef<'a,StackTop<'b>>,
                             inp_top: Transf<Em>,
                             ret: OptRef<'a,Option<V>>,
                             inp_ret: Transf<Em>)
                             -> (OptRef<'c,Thread<'b,V>>,Transf<Em>)
    where V : Bytes+FromConst<'b>+Clone,Em : Embed {
    debug_assert_eq!(cs.as_ref().num_elem(),inp_cs.size());
    debug_assert_eq!(st.as_ref().num_elem(),inp_st.size());
    debug_assert_eq!(top.as_ref().num_elem(),inp_top.size());
    debug_assert_eq!(ret.as_ref().num_elem(),inp_ret.size());
    (OptRef::Owned(Thread { call_stack: cs.as_obj(),
                            stack: st.as_obj(),
                            stack_top: top.as_obj(),
                            ret: ret.as_obj() }),
     Transformation::concat(&[inp_cs,inp_st,inp_top,inp_ret]))
}
                                 

pub fn decompose_thread<'a,'b,V,Em>(thr: OptRef<'a,Thread<'b,V>>,
                                    inp_thr: Transf<Em>)
                                    -> (OptRef<'a,CallStack<'b,V>>,
                                        Transf<Em>,
                                        OptRef<'a,Stack<'b,V>>,
                                        Transf<Em>,
                                        OptRef<'a,StackTop<'b>>,
                                        Transf<Em>,
                                        OptRef<'a,Option<V>>,
                                        Transf<Em>)
    where V : Bytes+FromConst<'b>+Clone,Em : Embed {
    let (cs,st,top,ret) = match thr {
        OptRef::Ref(ref rthr)
            => (OptRef::Ref(&rthr.call_stack),
                OptRef::Ref(&rthr.stack),
                OptRef::Ref(&rthr.stack_top),
                OptRef::Ref(&rthr.ret)),
        OptRef::Owned(rthr)
            => (OptRef::Owned(rthr.call_stack),
                OptRef::Owned(rthr.stack),
                OptRef::Owned(rthr.stack_top),
                OptRef::Owned(rthr.ret))
    };
    let sz_cs = cs.as_ref().num_elem();
    let inp_cs = Transformation::view(0,sz_cs,inp_thr.clone());
    let sz_st = st.as_ref().num_elem();
    let inp_st = Transformation::view(sz_cs,sz_st,inp_thr.clone());
    let sz_top = top.as_ref().num_elem();
    let inp_top = Transformation::view(sz_cs+sz_st,sz_top,inp_thr.clone());
    let sz_ret = ret.as_ref().num_elem();
    let inp_ret = Transformation::view(sz_cs+sz_st+sz_top,sz_ret,inp_thr);
    (cs,inp_cs,st,inp_st,top,inp_top,ret,inp_ret)
}*/

impl<'b,V: HasSorts> HasSorts for Thread<'b,V> {
    fn num_elem(&self) -> usize {
        self.call_stack.num_elem() +
            self.stack.num_elem() +
            self.stack_top.num_elem() +
            self.ret.num_elem()
    }
    fn elem_sort<Em : Embed>(&self,pos: usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        let off1 = self.call_stack.num_elem();
        if pos<off1 {
            return self.call_stack.elem_sort(pos,em)
        }
        let off2 = off1+self.stack.num_elem();
        if pos<off2 {
            return self.stack.elem_sort(pos-off1,em)
        }
        let off3 = off2+self.stack_top.num_elem();
        if pos<off3 {
            return self.stack_top.elem_sort(pos-off2,em)
        }
        debug_assert!({ let off4 = off3+self.ret.num_elem();
                        pos<off4 });
        self.ret.elem_sort(pos-off3,em)
    }
}

impl<'a,V: Bytes<'a>+FromConst<'a>+Debug> Composite<'a> for Thread<'a,V> {
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

        let cs_l = pl.clone().then(Self::call_stack());
        let cs_r = pr.clone().then(Self::call_stack());

        let ncs = match CallStack::combine(&cs_l,froml,arrl,
                                           &cs_r,fromr,arrr,
                                           comb,only_l,only_r,
                                           res,em)? {
            None => return Ok(None),
            Some(r) => r
        };

        let st_l = pl.clone().then(Self::stack());
        let st_r = pr.clone().then(Self::stack());

        let nst = match Stack::combine(&st_l,froml,arrl,
                                       &st_r,fromr,arrr,
                                       comb,only_l,only_r,
                                       res,em)? {
            None => return Ok(None),
            Some(r) => r
        };

        let top_l = pl.clone().then(Self::stack_top());
        let top_r = pr.clone().then(Self::stack_top());

        let ntop = match StackTop::combine(&top_l,froml,arrl,
                                           &top_r,fromr,arrr,
                                           comb,only_l,only_r,
                                           res,em)? {
            None => return Ok(None),
            Some(r) => r
        };

        let ret_l = pl.clone().then(Self::ret());
        let ret_r = pr.clone().then(Self::ret());

        let nret = match Option::combine(&ret_l,froml,arrl,
                                         &ret_r,fromr,arrr,
                                         comb,only_l,only_r,
                                         res,em)? {
            None => return Ok(None),
            Some(r) => r
        };

        Ok(Some(Thread { call_stack: ncs,
                         stack: nst,
                         stack_top: ntop,
                         ret: nret }))
    }
}

#[derive(Clone,PartialEq,Eq,Debug)]
pub struct CallStackPath;

#[derive(Clone,PartialEq,Eq,Debug)]
pub struct StackPath;

#[derive(Clone,PartialEq,Eq,Debug)]
pub struct StackTopPath;

#[derive(Clone,PartialEq,Eq,Debug)]
pub struct RetPath;

impl CallStackPath {
    pub fn new() -> Self {
        CallStackPath
    }
}

impl StackPath {
    pub fn new() -> Self {
        StackPath
    }
}

impl StackTopPath {
    pub fn new() -> Self {
        StackTopPath
    }
}

impl RetPath {
    pub fn new() -> Self {
        RetPath
    }
}

impl<'a,V> SimplePathEl<'a,Thread<'a,V>> for CallStackPath
    where V: 'a {
    type To = CallStack<'a,V>;
    fn get<'b>(&self,obj: &'b Thread<'a,V>)
               -> &'b Self::To where 'a: 'b {
        &obj.call_stack
    }
    fn get_mut<'c>(&self,from: &'c mut Thread<'a,V>)
                   -> &'c mut Self::To where 'a: 'c {
        &mut from.call_stack
    }
}

impl<'a,Em: Embed,V> PathEl<'a,Em,Thread<'a,V>> for CallStackPath
    where V: 'a+HasSorts+Clone {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Thread<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        prev.read(prev_from,pos,arr,em)
    }
    fn read_slice<'c,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Thread<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        len: usize,
        arr: &'c [Em::Expr])
        -> Option<&'c [Em::Expr]> {
        prev.read_slice(prev_from,pos,len,arr)
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Thread<'a,V>>>(
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
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Thread<'a,V>>>(
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

impl<'a,V> SimplePathEl<'a,Thread<'a,V>> for StackPath
    where V: 'a {
    type To = Stack<'a,V>;
        fn get<'c>(&self,from: &'c Thread<'a,V>) -> &'c Self::To where 'a: 'c {
        &from.stack
    }
    fn get_mut<'c>(&self,from: &'c mut Thread<'a,V>) -> &'c mut Self::To where 'a: 'c {
        &mut from.stack
    }
}

impl<'a,Em: Embed,V> PathEl<'a,Em,Thread<'a,V>> for StackPath
    where V: 'a+HasSorts+Clone {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Thread<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        let off = prev.get(prev_from).call_stack.num_elem();
        prev.read(prev_from,pos+off,arr,em)
    }
    fn read_slice<'c,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Thread<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        len: usize,
        arr: &'c [Em::Expr])
        -> Option<&'c [Em::Expr]> {
        let off = prev.get(prev_from).call_stack.num_elem();
        prev.read_slice(prev_from,pos+off,len,arr)
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Thread<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        e: Em::Expr,
        arr: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        let off = prev.get(prev_from).call_stack.num_elem();
        prev.write(prev_from,pos+off,e,arr,em)
    }
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Thread<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &mut PrevFrom,
        pos: usize,
        old_len: usize,
        src: &mut Vec<Em::Expr>,
        trg: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        let off = prev.get(prev_from).call_stack.num_elem();
        prev.write_slice(prev_from,pos+off,old_len,src,trg,em)
    }
}

impl<'a,V> SimplePathEl<'a,Thread<'a,V>> for StackTopPath
    where V: 'a {
    type To = StackTop<'a>;
    fn get<'c>(&self,from: &'c Thread<'a,V>) -> &'c Self::To where 'a: 'c {
        &from.stack_top
    }
    fn get_mut<'c>(&self,from: &'c mut Thread<'a,V>) -> &'c mut Self::To where 'a: 'c {
        &mut from.stack_top
    }
}

impl<'a,Em: Embed,V> PathEl<'a,Em,Thread<'a,V>> for StackTopPath
    where V: 'a+HasSorts+Clone {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Thread<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        let off = {
            let from = prev.get(prev_from);
            from.call_stack.num_elem()
                + from.stack.num_elem()
        };
        prev.read(prev_from,pos+off,arr,em)
    }
    fn read_slice<'c,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Thread<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        len: usize,
        arr: &'c [Em::Expr])
        -> Option<&'c [Em::Expr]> {
        let off = {
            let from = prev.get(prev_from);
            from.call_stack.num_elem()
                + from.stack.num_elem()
        };
        prev.read_slice(prev_from,pos+off,len,arr)
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Thread<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        e: Em::Expr,
        arr: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        let off = {
            let from = prev.get(prev_from);
            from.call_stack.num_elem()
                + from.stack.num_elem()
        };
        prev.write(prev_from,pos+off,e,arr,em)
    }
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Thread<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &mut PrevFrom,
        pos: usize,
        old_len: usize,
        src: &mut Vec<Em::Expr>,
        trg: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        let off = {
            let from = prev.get(prev_from);
            from.call_stack.num_elem()
                + from.stack.num_elem()
        };
        prev.write_slice(prev_from,pos+off,old_len,src,trg,em)
    }
}

impl<'a,V> SimplePathEl<'a,Thread<'a,V>> for RetPath
    where V: 'a {
    type To = Option<V>;
    fn get<'c>(&self,from: &'c Thread<'a,V>) -> &'c Self::To where 'a: 'c {
        &from.ret
    }
    fn get_mut<'c>(&self,from: &'c mut Thread<'a,V>) -> &'c mut Self::To where 'a: 'c {
        &mut from.ret
    }
}

impl<'a,Em: Embed,V> PathEl<'a,Em,Thread<'a,V>> for RetPath
    where V: 'a+HasSorts+Clone {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Thread<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        let off = {
            let from = prev.get(prev_from);
            from.call_stack.num_elem()
                + from.stack.num_elem()
                + from.stack_top.num_elem()
        };
        prev.read(prev_from,pos+off,arr,em)
    }
    fn read_slice<'c,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Thread<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        len: usize,
        arr: &'c [Em::Expr])
        -> Option<&'c [Em::Expr]> {
        let off = {
            let from = prev.get(prev_from);
            from.call_stack.num_elem()
                + from.stack.num_elem()
                + from.stack_top.num_elem()
        };
        prev.read_slice(prev_from,pos+off,len,arr)
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Thread<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        e: Em::Expr,
        arr: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        let off = {
            let from = prev.get(prev_from);
            from.call_stack.num_elem()
                + from.stack.num_elem()
                + from.stack_top.num_elem()
        };
        prev.write(prev_from,pos+off,e,arr,em)
    }
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Thread<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &mut PrevFrom,
        pos: usize,
        old_len: usize,
        src: &mut Vec<Em::Expr>,
        trg: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        let off = {
            let from = prev.get(prev_from);
            from.call_stack.num_elem()
                + from.stack.num_elem()
                + from.stack_top.num_elem()
        };
        prev.write_slice(prev_from,pos+off,old_len,src,trg,em)
    }
}

/*

pub type CallFrameView<'a,V>
    = Then<CallStackView<'a,V>,
           Then<AssocView<CallId<'a>,
                          BitVecVectorStack<(CallFrame<'a,V>,Frame<'a,V>)>>,
                Then<BitVecVectorStackView<(CallFrame<'a,V>,Frame<'a,V>)>,
                     FstView<CallFrame<'a,V>,Frame<'a,V>>>>>;
*/
#[derive(Clone)]
pub enum FramePath<Prev> {
    Call(Then<Then<Then<Then<Then<Prev,CallStackPath>,
                             AssocP>,
                        BitVecVectorStackElements>,
                   CompVecP>,
              Element2Of2>),
    Stack(Then<Then<Then<Then<Prev,
                              StackPath>,
                         AssocP>,
                    BitVecVectorStackElements>,
               CompVecP>)
}

pub enum FrameAccess<'a,From: 'a,Prev,V: 'a,Em: DeriveValues> {
    Call(DynBitVecVectorStackAccess
         <Then<Then<Prev,CallStackPath>,
               AssocP>,Em>,
         PhantomData<&'a (From,V)>),
    Stack(DynBitVecVectorStackAccess
          <Then<Then<Prev,
                     StackPath>,
                AssocP>,Em>,
          PhantomData<&'a (From,V)>)
}

impl<'a,From,Prev,V,Em> FrameAccess<'a,From,Prev,V,Em>
    where
    Em: DeriveValues {
    pub fn new(path: Prev,
               from: &From,
               from_arr: &[Em::Expr],
               id: &FrameId<'a>,
               em: &mut Em) -> Result<Self,Em::Error>
        where Prev: Path<'a,Em,From,To=Thread<'a,V>>,
              V: 'a+HasSorts+Clone {
        match id {
            &FrameId::Call(ref cid) => {
                let npath = Assoc::lookup(then(path,CallStackPath),
                                          from,cid)
                    .expect("Call frame not found");
                let acc = BitVecVectorStack::top(npath,from,from_arr,em)?;
                Ok(FrameAccess::Call(acc,PhantomData))
            },
            &FrameId::Stack(ref sid) => {
                let npath = Assoc::lookup(then(path,StackPath),
                                          from,sid)
                    .expect("Frame not found");
                let acc = BitVecVectorStack::top(npath,from,from_arr,em)?;
                Ok(FrameAccess::Stack(acc,PhantomData))
            }
        }
    }
}

/*
pub fn frame_view_to_idx<'a,V,Em : Embed>(view: &FrameView<'a,V>,bw: usize,em: &mut Em)
                                          -> Result<(FrameId<'a>,Transf<Em>),Em::Error> {
    match view {
        &FrameView::Call(Then(_,Then(ref cid,Then(ref vec,_)))) => {
            let e = em.const_bitvec(bw,BigUint::from(vec.idx))?;
            let inp = Transformation::constant(vec![e]);
            Ok((FrameId::Call(cid.key.clone()),inp))
        },
        &FrameView::Stack(Then(_,Then(ref iid,ref vec))) => {
            let e = em.const_bitvec(bw,BigUint::from(vec.idx))?;
            let inp = Transformation::constant(vec![e]);
            Ok((FrameId::Stack(iid.key.clone()),inp))
        }
    }
}*/

impl<'a,PrevFrom,Prev: SimplePath<'a,PrevFrom,To=Thread<'a,V>>,V
     > SimplePath<'a,PrevFrom> for FramePath<Prev>
    where V: 'a+HasSorts {

    type To   = Frame<'a,V>;

    fn get<'b>(&self,from: &'b PrevFrom)
               -> &'b Self::To where 'a: 'b {
        match self {
            &FramePath::Call(ref p) => p.get(from),
            &FramePath::Stack(ref p) => p.get(from)
        }
    }
    fn get_mut<'b>(&self,from: &'b mut PrevFrom) -> &'b mut Self::To where 'a: 'b {
        match self {
            &FramePath::Call(ref p) => p.get_mut(from),
            &FramePath::Stack(ref p) => p.get_mut(from)
        }
    }
}

impl<'a,Em: Embed,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Thread<'a,V>>,V
     > Path<'a,Em,PrevFrom> for FramePath<Prev>
    where V: 'a+HasSorts+Clone {

    fn read(&self,from: &PrevFrom,pos: usize,arr: &[Em::Expr],em: &mut Em)
            -> Result<Em::Expr,Em::Error> {
        match self {
            &FramePath::Call(ref p) => p.read(from,pos,arr,em),
            &FramePath::Stack(ref p) => p.read(from,pos,arr,em)
        }
    }
    fn read_slice<'b>(&self,from: &PrevFrom,pos: usize,len: usize,arr: &'b [Em::Expr])
                     -> Option<&'b [Em::Expr]> {
        match self {
            &FramePath::Call(ref p) => p.read_slice(from,pos,len,arr),
            &FramePath::Stack(ref p) => p.read_slice(from,pos,len,arr)
        }
    }
    fn write(&self,from: &PrevFrom,
             pos: usize,expr: Em::Expr,
             arr: &mut Vec<Em::Expr>,em: &mut Em)
             -> Result<(),Em::Error> {
        match self {
            &FramePath::Call(ref p) => p.write(from,pos,expr,arr,em),
            &FramePath::Stack(ref p) => p.write(from,pos,expr,arr,em)
        }
    }
    fn write_slice(&self,
                   from: &mut PrevFrom,
                   pos: usize,
                   old_len: usize,
                   src: &mut Vec<Em::Expr>,
                   trg: &mut Vec<Em::Expr>,
                   em: &mut Em)
                   -> Result<(),Em::Error> {
        match self {
            &FramePath::Call(ref p) => p.write_slice(from,pos,old_len,src,trg,em),
            &FramePath::Stack(ref p) => p.write_slice(from,pos,old_len,src,trg,em)
        }
    }
}

impl<'a,From,Prev,V,Em> CondIterator<Em> for FrameAccess<'a,From,Prev,V,Em>
    where
    Prev: Path<'a,Em,From,To=Thread<'a,V>>,
    Em: DeriveValues {
    type Item = FramePath<Prev>;
    fn next(&mut self,conds: &mut Vec<Em::Expr>,cond_pos: usize,em: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        match self {
            &mut FrameAccess::Call(ref mut acc,_)
                => match acc.next(conds,cond_pos,em)? {
                    None => Ok(None),
                    Some(path) => {
                        let rpath = FramePath::Call(then(path,Element2Of2));
                        Ok(Some(rpath))
                    }
                },
            &mut FrameAccess::Stack(ref mut acc,_)
                => match acc.next(conds,cond_pos,em)? {
                    None => Ok(None),
                    Some(path) => {
                        let rpath = FramePath::Stack(path);
                        Ok(Some(rpath))
                    }
                }
        }
    }
}

#[derive(Clone)]
pub enum ThreadMeaning<'b,V: Semantic+Bytes<'b>+FromConst<'b>> {
    CallStack(<CallStack<'b,V> as Semantic>::Meaning),
    Stack(<Stack<'b,V> as Semantic>::Meaning),
    StackTop(<StackTop<'b> as Semantic>::Meaning),
    Ret(<Option<V> as Semantic>::Meaning)
}

pub enum ThreadMeaningCtx<'b,V: Semantic+Bytes<'b>+FromConst<'b>> {
    CallStack(<CallStack<'b,V> as Semantic>::MeaningCtx),
    Stack(<Stack<'b,V> as Semantic>::MeaningCtx),
    StackTop(<StackTop<'b> as Semantic>::MeaningCtx),
    Ret(<Option<V> as Semantic>::MeaningCtx)
}

impl<'b,V : Semantic+Bytes<'b>+FromConst<'b>> PartialEq for ThreadMeaning<'b,V> {
    fn eq(&self,other: &ThreadMeaning<'b,V>) -> bool {
        match self {
            &ThreadMeaning::CallStack(ref p) => match other {
                &ThreadMeaning::CallStack(ref q) => p.eq(q),
                _ => false
            },
            &ThreadMeaning::Stack(ref p) => match other {
                &ThreadMeaning::Stack(ref q) => p.eq(q),
                _ => false
            },
            &ThreadMeaning::StackTop(ref p) => match other {
                &ThreadMeaning::StackTop(ref q) => p.eq(q),
                _ => false
            },
            &ThreadMeaning::Ret(ref p) => match other {
                &ThreadMeaning::Ret(ref q) => p.eq(q),
                _ => false
            }
        }
    }
}

impl<'b,V: Semantic+Bytes<'b>+FromConst<'b>> Eq for ThreadMeaning<'b,V> {}

impl<'b,V: Semantic+Bytes<'b>+FromConst<'b>> PartialOrd for ThreadMeaning<'b,V> {
    fn partial_cmp(&self,other: &ThreadMeaning<'b,V>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<'b,V: Semantic+Bytes<'b>+FromConst<'b>> Ord for ThreadMeaning<'b,V> {
    fn cmp(&self,other: &ThreadMeaning<'b,V>) -> Ordering {
        match (self,other) {
            (&ThreadMeaning::CallStack(ref p),
             &ThreadMeaning::CallStack(ref q)) => p.cmp(q),
            (&ThreadMeaning::CallStack(_),_) => Ordering::Less,
            (_,&ThreadMeaning::CallStack(_)) => Ordering::Greater,
            (&ThreadMeaning::Stack(ref p),
             &ThreadMeaning::Stack(ref q)) => p.cmp(q),
            (&ThreadMeaning::Stack(_),_) => Ordering::Less,
            (_,&ThreadMeaning::Stack(_)) => Ordering::Greater,
            (&ThreadMeaning::StackTop(ref p),
             &ThreadMeaning::StackTop(ref q)) => p.cmp(q),
            (&ThreadMeaning::StackTop(_),_) => Ordering::Less,
            (_,&ThreadMeaning::StackTop(_)) => Ordering::Greater,
            (&ThreadMeaning::Ret(ref p),
             &ThreadMeaning::Ret(ref q)) => p.cmp(q),
        }
    }
}

impl<'b,V: Semantic+Bytes<'b>+FromConst<'b>> Hash for ThreadMeaning<'b,V> {
    fn hash<H>(&self, state: &mut H) where H: Hasher {
        match self {
            &ThreadMeaning::CallStack(ref p) => {
                (0 as u8).hash(state);
                p.hash(state);
            },
            &ThreadMeaning::Stack(ref p) => {
                (1 as u8).hash(state);
                p.hash(state);
            },
            &ThreadMeaning::StackTop(ref p) => {
                (2 as u8).hash(state);
                p.hash(state);
            },
            &ThreadMeaning::Ret(ref p) => {
                (3 as u8).hash(state);
                p.hash(state);
            }
        }
    }
}

impl<'b,V: Semantic+Bytes<'b>+FromConst<'b>> fmt::Debug for ThreadMeaning<'b,V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            &ThreadMeaning::CallStack(ref p) => f.debug_tuple("CallStack")
                .field(p).finish(),
            &ThreadMeaning::Stack(ref p) => f.debug_tuple("Stack")
                .field(p).finish(),
            &ThreadMeaning::StackTop(ref p) => f.debug_tuple("StackTop")
                .field(p).finish(),
            &ThreadMeaning::Ret(ref p) => f.debug_tuple("Ret")
                .field(p).finish()
        }
    }
}

impl<'b,V: Semantic+Bytes<'b>+FromConst<'b>> ThreadMeaning<'b,V> {
    pub fn is_pc(&self) -> bool {
        match self {
            &ThreadMeaning::CallStack(ref m) => match m.meaning {
                BitVecVectorStackMeaning::Top => true,
                BitVecVectorStackMeaning::Elem(VecMeaning {
                    ref meaning,..
                }) => match meaning {
                    &TupleMeaning::Fst(ref m) => m.is_pc(),
                    &TupleMeaning::Snd(ref m) => m.is_pc()
                }
            },
            &ThreadMeaning::Stack(ref m) => match m.meaning {
                BitVecVectorStackMeaning::Top => true,
                BitVecVectorStackMeaning::Elem(VecMeaning {
                    ref meaning,..
                }) => meaning.is_pc()
            },
            &ThreadMeaning::StackTop(_) => true,
            &ThreadMeaning::Ret(_) => false
        }
    }
}

impl<'b,V: Semantic+Bytes<'b>+FromConst<'b>> Semantic for Thread<'b,V> {
    type Meaning = ThreadMeaning<'b,V>;
    type MeaningCtx = ThreadMeaningCtx<'b,V>;
    fn meaning(&self,pos: usize) -> Self::Meaning {
        let off1 = self.call_stack.num_elem();
        if pos<off1 {
            return ThreadMeaning::CallStack(self.call_stack.meaning(pos))
        }
        let off2 = off1+self.stack.num_elem();
        if pos<off2 {
            return ThreadMeaning::Stack(self.stack.meaning(pos-off1))
        }
        let off3 = off2+self.stack_top.num_elem();
        if pos<off3 {
            return ThreadMeaning::StackTop(self.stack_top.meaning(pos-off2))
        }
        ThreadMeaning::Ret(self.ret.meaning(pos-off3))
    }
    fn fmt_meaning<F : fmt::Write>(&self,m: &Self::Meaning,fmt: &mut F) -> Result<(),fmt::Error> {
        match m {
            &ThreadMeaning::CallStack(ref nm) => {
                write!(fmt,"cs.")?;
                self.call_stack.fmt_meaning(nm,fmt)
            },
            &ThreadMeaning::Stack(ref nm) => {
                write!(fmt,"st.")?;
                self.stack.fmt_meaning(nm,fmt)
            },
            &ThreadMeaning::StackTop(ref nm) => {
                write!(fmt,"top.")?;
                self.stack_top.fmt_meaning(nm,fmt)
            },
            &ThreadMeaning::Ret(ref nm) => {
                write!(fmt,"ret.")?;
                self.ret.fmt_meaning(nm,fmt)
            }
        }
    }
    fn first_meaning(&self) -> Option<(Self::MeaningCtx,Self::Meaning)> {
        if let Some((ctx,m)) = self.call_stack.first_meaning() {
            Some((ThreadMeaningCtx::CallStack(ctx),
                  ThreadMeaning::CallStack(m)))
        } else if let Some((ctx,m)) = self.stack.first_meaning() {
            Some((ThreadMeaningCtx::Stack(ctx),
                  ThreadMeaning::Stack(m)))
        } else if let Some((ctx,m)) = self.stack_top.first_meaning() {
            Some((ThreadMeaningCtx::StackTop(ctx),
                  ThreadMeaning::StackTop(m)))
        } else if let Some((ctx,m)) = self.ret.first_meaning() {
            Some((ThreadMeaningCtx::Ret(ctx),
                  ThreadMeaning::Ret(m)))
        } else {
            None
        }
    }
    fn next_meaning(&self,ctx: &mut Self::MeaningCtx,m: &mut Self::Meaning) -> bool {
        let (nctx,nm) = match ctx {
            &mut ThreadMeaningCtx::CallStack(ref mut cctx) => match m {
                &mut ThreadMeaning::CallStack(ref mut cm) => if self.call_stack.next_meaning(cctx,cm) {
                    return true
                } else if let Some((ctx,m)) = self.stack.first_meaning() {
                    (ThreadMeaningCtx::Stack(ctx),
                     ThreadMeaning::Stack(m))
                } else if let Some((ctx,m)) = self.stack_top.first_meaning() {
                    (ThreadMeaningCtx::StackTop(ctx),
                     ThreadMeaning::StackTop(m))
                } else if let Some((ctx,m)) = self.ret.first_meaning() {
                    (ThreadMeaningCtx::Ret(ctx),
                     ThreadMeaning::Ret(m))
                } else {
                    return false
                },
                _ => unreachable!()
            },
            &mut ThreadMeaningCtx::Stack(ref mut cctx) => match m {
                &mut ThreadMeaning::Stack(ref mut cm) => if self.stack.next_meaning(cctx,cm) {
                    return true
                } else if let Some((ctx,m)) = self.stack_top.first_meaning() {
                    (ThreadMeaningCtx::StackTop(ctx),
                     ThreadMeaning::StackTop(m))
                } else if let Some((ctx,m)) = self.ret.first_meaning() {
                    (ThreadMeaningCtx::Ret(ctx),
                     ThreadMeaning::Ret(m))
                } else {
                    return false
                },
                _ => unreachable!()
            },
            &mut ThreadMeaningCtx::StackTop(ref mut cctx) => match m {
                &mut ThreadMeaning::StackTop(ref mut cm) => if self.stack_top.next_meaning(cctx,cm) {
                    return true
                } else if let Some((ctx,m)) = self.ret.first_meaning() {
                    (ThreadMeaningCtx::Ret(ctx),
                     ThreadMeaning::Ret(m))
                } else {
                    return false
                },
                _ => unreachable!()
            },
            &mut ThreadMeaningCtx::Ret(ref mut cctx) => match m {
                &mut ThreadMeaning::Ret(ref mut cm) => return self.ret.next_meaning(cctx,cm),
                _ => unreachable!()
            }
        };
        *ctx = nctx;
        *m = nm;
        true
    }
}

