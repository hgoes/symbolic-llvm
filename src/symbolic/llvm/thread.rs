extern crate smtrs;

use self::smtrs::composite::*;
use self::smtrs::embed::{Embed,DeriveConst};
use super::mem::{Bytes,FromConst};
use super::frame::*;
use super::{InstructionRef};
use std::marker::PhantomData;
use num_bigint::BigInt;
use std::ops::Range;

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

enum CallStackDataVars<'a,'b : 'a,V : 'b> {
    CallFrame(CallFrameDataVars<'a,'b,V>),
    Frame(Range<usize>)
}

enum ThreadDataVarsPos<'a,'b : 'a,V : 'b> {
    CallStack { assoc_nr: usize,
                stack_nr: usize,
                iter: CallStackDataVars<'a,'b,V> },
    Stack { assoc_nr: usize,
            stack_nr: usize,
            iter: Range<usize> },
    Ret(Range<usize>)
}

pub struct ThreadDataVars<'a,'b : 'a,V : 'b> {
    off: usize,
    thread: &'a Thread<'b,V>,
    iter: ThreadDataVarsPos<'a,'b,V>
}

impl<'a,'b,V : Bytes+FromConst<'b>> Iterator for ThreadDataVars<'a,'b,V> {
    type Item = usize;
    fn next(&mut self) -> Option<usize> {
        'outer: loop {
            let niter = match self.iter {
                ThreadDataVarsPos::CallStack { ref mut assoc_nr, ref mut stack_nr, ref mut iter } => {
                    let niter = match iter {
                        &mut CallStackDataVars::CallFrame(ref mut siter) => match siter.next() {
                            Some(r) => return Some(r),
                            None => {
                                let &(_,ref frs) = self.thread.call_stack.entry(*assoc_nr);
                                let &(_,ref fr) = frs.entry(*stack_nr);
                                let (fr_sz,niter) = fr.data_vars(self.off);
                                self.off+=fr_sz;
                                Some(CallStackDataVars::Frame(niter))
                            }
                        },
                        &mut CallStackDataVars::Frame(ref mut siter) => match siter.next() {
                            Some(r) => return Some(r),
                            None => None
                        }
                    };
                    match niter {
                        Some(it) => {
                            *iter = it;
                            continue
                        },
                        None => {
                            let &(_,ref st) = self.thread.call_stack.entry(*assoc_nr);
                            if *stack_nr+1<st.len() {
                                *stack_nr+=1;
                                let (sz,nit) = st.entry(*stack_nr).0.data_vars(self.off);
                                self.off+=sz;
                                *iter = CallStackDataVars::CallFrame(nit);
                                continue
                            }
                            for p in *assoc_nr+1..self.thread.call_stack.len() {
                                self.off+=1;
                                let cfs = &self.thread.call_stack.entry(p).1;
                                if cfs.len() > 0 {
                                    *assoc_nr = p;
                                    *stack_nr = 0;
                                    let &(ref cf,_) = cfs.entry(0);
                                    let (sz,nit) = cf.data_vars(self.off);
                                    self.off+=sz;
                                    *iter = CallStackDataVars::CallFrame(nit);
                                    continue 'outer
                                }
                            }
                            {
                                let mut nxt_fr = None;
                                for fr_pos in 0..self.thread.stack.len() {
                                    let entr = &self.thread.stack.entry(fr_pos).1;
                                    if entr.len() > 0 {
                                        let (sz,it) = entr.entry(0).data_vars(self.off);
                                        self.off+=sz;
                                        nxt_fr = Some((fr_pos,it));
                                        break
                                    }
                                }
                                match nxt_fr {
                                    None => return None,
                                    Some((pos,it)) => ThreadDataVarsPos::Stack { assoc_nr: pos,
                                                                                 stack_nr: 0,
                                                                                 iter: it }
                                }
                            }
                        }
                    }
                },
                ThreadDataVarsPos::Stack { ref mut assoc_nr, ref mut stack_nr, ref mut iter } => {
                    match iter.next() {
                        Some(r) => return Some(r),
                        None => {
                            let &(_,ref st) = self.thread.stack.entry(*assoc_nr);
                            if *stack_nr+1<st.len() {
                                *stack_nr+=1;
                                let (sz,nit) = st.entry(*stack_nr).data_vars(self.off);
                                self.off+=sz;
                                *iter = nit;
                                continue
                            }
                            for p in *assoc_nr+1..self.thread.stack.len() {
                                let cfs = &self.thread.stack.entry(p).1;
                                if cfs.len() > 0 {
                                    *assoc_nr = p;
                                    *stack_nr = 0;
                                    let (sz,nit) = cfs.entry(0).data_vars(self.off);
                                    self.off+=sz;
                                    *iter = nit;
                                    continue 'outer
                                }
                            }
                            let top_sz = self.thread.stack_top.num_elem();
                            let ret_sz = self.thread.ret.num_elem();
                            self.off+=top_sz;
                            let coff = self.off;
                            self.off+=ret_sz;
                            ThreadDataVarsPos::Ret(coff..coff+ret_sz)
                        }
                    }
                },
                ThreadDataVarsPos::Ret(ref mut it) => match it.next() {
                    Some(r) => return Some(r),
                    None => return None
                }
            };
            self.iter = niter;
        }
    }
}

impl<'a,V : Bytes+FromConst<'a>> Thread<'a,V> {
    pub fn data_vars<'b>(&'b self,mut off: usize) -> ThreadDataVars<'b,'a,V> {
        for cs_idx in 0..self.call_stack.len() {
            off+=1;
            let &(_,ref cs) = self.call_stack.entry(cs_idx);
            if cs.len()>0 {
                let &(ref cf,_) = cs.entry(0);
                let (sz,it) = cf.data_vars(off);
                return ThreadDataVars { off: off+sz,
                                        thread: self,
                                        iter: ThreadDataVarsPos::CallStack {
                                            assoc_nr: cs_idx,
                                            stack_nr: 0,
                                            iter: CallStackDataVars::CallFrame(it)
                                        }
                }
            }
        }
        for st_idx in 0..self.stack.len() {
            let st = &self.stack.entry(st_idx).1;
            if st.len()>0 {
                let fr = st.entry(0);
                let (sz,it) = fr.data_vars(off);
                return ThreadDataVars { off: off+sz,
                                        thread: self,
                                        iter: ThreadDataVarsPos::Stack {
                                            assoc_nr: st_idx,
                                            stack_nr: 0,
                                            iter: it
                                        }
                }
            }
        }
        let top_sz = self.stack_top.num_elem();
        let ret_sz = self.ret.num_elem();
        ThreadDataVars { off: off+top_sz,
                         thread: self,
                         iter: ThreadDataVarsPos::Ret(off+top_sz..off+top_sz+ret_sz) }
    }
}

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
}

impl<'b,V : Bytes+FromConst<'b>> Composite for Thread<'b,V> {
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
    fn combine<'a,Em,FComb,FL,FR>(x: OptRef<'a,Self>,y: OptRef<'a,Self>,
                                  inp_x: Transf<Em>,inp_y: Transf<Em>,
                                  comb: &FComb,only_l: &FL,only_r: &FR,em: &mut Em)
                                  -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>
        where Em : Embed,
              FComb : Fn(Transf<Em>,Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FL : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FR : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error> {
        let (cs_x,inp_cs_x,st_x,inp_st_x,top_x,inp_top_x,ret_x,inp_ret_x) = decompose_thread(x,inp_x);
        let (cs_y,inp_cs_y,st_y,inp_st_y,top_y,inp_top_y,ret_y,inp_ret_y) = decompose_thread(y,inp_y);
        let (cs,inp_cs) = match Assoc::combine(cs_x,cs_y,
                                               inp_cs_x,inp_cs_y,
                                               comb,only_l,only_r,em)? {
            None => return Ok(None),
            Some(r) => r
        };
        let (st,inp_st) = match Assoc::combine(st_x,st_y,
                                               inp_st_x,inp_st_y,
                                               comb,only_l,only_r,em)? {
            None => return Ok(None),
            Some(r) => r
        };
        let (top,inp_top) = match Choice::combine(top_x,top_y,
                                                  inp_top_x,inp_top_y,
                                                  comb,only_l,only_r,em)? {
            None => return Ok(None),
            Some(r) => r
        };
        let (ret,inp_ret) = match Option::combine(ret_x,ret_y,
                                                  inp_ret_x,inp_ret_y,
                                                  comb,only_l,only_r,em)? {
            None => return Ok(None),
            Some(r) => r
        };
        Ok(Some((OptRef::Owned(Thread { call_stack: cs.as_obj(),
                                        stack: st.as_obj(),
                                        stack_top: top.as_obj(),
                                        ret: ret.as_obj() }),
                 Transformation::concat(&[inp_cs,inp_st,inp_top,inp_ret]))))
    }
}

#[derive(PartialEq,Eq,Debug)]
pub struct CallStackView<'a,V : 'a>(PhantomData<&'a V>);

impl<'a,V : 'a> Clone for CallStackView<'a,V> {
    fn clone(&self) -> Self {
        CallStackView(PhantomData)
    }
}

#[derive(PartialEq,Eq,Debug)]
pub struct StackView<'a,V : 'a>(PhantomData<&'a V>);

impl<'a,V : 'a> Clone for StackView<'a,V> {
    fn clone(&self) -> Self {
        StackView(PhantomData)
    }
}

#[derive(PartialEq,Eq,Debug)]
pub struct StackTopView<'a,V : 'a>(PhantomData<&'a V>);

impl<'a,V : 'a> Clone for StackTopView<'a,V> {
    fn clone(&self) -> Self {
        StackTopView(PhantomData)
    }
}

#[derive(PartialEq,Eq,Debug)]
pub struct RetView<'a,V : 'a>(PhantomData<&'a V>);

impl<'a,V : 'a> Clone for RetView<'a,V> {
    fn clone(&self) -> Self {
        RetView(PhantomData)
    }
}

impl<'a,V> CallStackView<'a,V> {
    pub fn new() -> Self {
        CallStackView(PhantomData)
    }
}

impl<'a,V> StackView<'a,V> {
    pub fn new() -> Self {
        StackView(PhantomData)
    }
}

impl<'a,V> StackTopView<'a,V> {
    pub fn new() -> Self {
        StackTopView(PhantomData)
    }
}

impl<'a,V> RetView<'a,V> {
    pub fn new() -> Self {
        RetView(PhantomData)
    }
}

impl<'a,V> View for CallStackView<'a,V>
    where V : 'a+Bytes+FromConst<'a> {
    type Viewed = Thread<'a,V>;
    type Element = CallStack<'a,V>;
    fn get_el<'b>(&self,obj: &'b Self::Viewed)
                  -> &'b Self::Element where Self : 'b {
        &obj.call_stack
    }
    fn get_el_ext<'b>(&self,obj: &'b Self::Viewed)
                      -> (usize,&'b Self::Element) where Self : 'b {
        (0,&obj.call_stack)
    }
}

impl<'a,V> View for StackView<'a,V>
    where V : 'a+Bytes+FromConst<'a> {
    type Viewed = Thread<'a,V>;
    type Element = Stack<'a,V>;
    fn get_el<'b>(&self,obj: &'b Self::Viewed)
                  -> &'b Self::Element where Self : 'b {
        &obj.stack
    }
    fn get_el_ext<'b>(&self,obj: &'b Self::Viewed)
                      -> (usize,&'b Self::Element) where Self : 'b {
        (obj.call_stack.num_elem(),&obj.stack)
    }
}

impl<'a,V> View for StackTopView<'a,V>
    where V : Bytes+FromConst<'a> {
    type Viewed = Thread<'a,V>;
    type Element = StackTop<'a>;
    fn get_el<'b>(&self,obj: &'b Self::Viewed)
                  -> &'b Self::Element where Self : 'b {
        &obj.stack_top
    }
    fn get_el_ext<'b>(&self,obj: &'b Self::Viewed)
                      -> (usize,&'b Self::Element) where Self : 'b {
        (obj.call_stack.num_elem()+
         obj.stack.num_elem(),&obj.stack_top)
    }
}

impl<'a,V> View for RetView<'a,V>
    where V : 'a+Bytes+FromConst<'a> {
    type Viewed = Thread<'a,V>;
    type Element = Option<V>;
    fn get_el<'b>(&self,obj: &'b Self::Viewed)
                  -> &'b Self::Element where Self : 'b {
        &obj.ret
    }
    fn get_el_ext<'b>(&self,obj: &'b Self::Viewed)
                      -> (usize,&'b Self::Element) where Self : 'b {
        (obj.call_stack.num_elem()+
         obj.stack.num_elem()+
         obj.stack_top.num_elem(),&obj.ret)
    }
}

impl<'a,V> ViewMut for CallStackView<'a,V>
    where V : 'a+Bytes+FromConst<'a> {
    fn get_el_mut<'b>(&self,obj: &'b mut Self::Viewed)
                      -> &'b mut Self::Element where Self : 'b {
        &mut obj.call_stack
    }
    fn get_el_mut_ext<'b>(&self,obj: &'b mut Self::Viewed)
                          -> (usize,&'b mut Self::Element)
        where Self : 'b {
        (0,&mut obj.call_stack)
    }
}

impl<'a,V> ViewMut for StackView<'a,V>
    where V : 'a+Bytes+FromConst<'a> {
    fn get_el_mut<'b>(&self,obj: &'b mut Self::Viewed)
                      -> &'b mut Self::Element where Self : 'b {
        &mut obj.stack
    }
    fn get_el_mut_ext<'b>(&self,obj: &'b mut Self::Viewed)
                          -> (usize,&'b mut Self::Element)
        where Self : 'b {
        (obj.call_stack.num_elem(),&mut obj.stack)
    }
}

impl<'a,V> ViewMut for StackTopView<'a,V>
    where V : 'a+Bytes+FromConst<'a> {
    fn get_el_mut<'b>(&self,obj: &'b mut Self::Viewed)
                      -> &'b mut Self::Element where Self : 'b {
        &mut obj.stack_top
    }
    fn get_el_mut_ext<'b>(&self,obj: &'b mut Self::Viewed)
                          -> (usize,&'b mut Self::Element)
        where Self : 'b {
        (obj.call_stack.num_elem()+
         obj.stack.num_elem(),&mut obj.stack_top)
    }
}

impl<'a,V> ViewMut for RetView<'a,V>
    where V : 'a+Bytes+FromConst<'a> {
    fn get_el_mut<'b>(&self,obj: &'b mut Self::Viewed)
                      -> &'b mut Self::Element where Self : 'b {
        &mut obj.ret
    }
    fn get_el_mut_ext<'b>(&self,obj: &'b mut Self::Viewed)
                          -> (usize,&'b mut Self::Element)
        where Self : 'b {
        (obj.call_stack.num_elem()+
         obj.stack.num_elem()+
         obj.stack_top.num_elem(),&mut obj.ret)
    }
}

pub type CallFrameView<'a,V>
    = Then<CallStackView<'a,V>,
           Then<AssocView<CallId<'a>,
                          BitVecVectorStack<(CallFrame<'a,V>,Frame<'a,V>)>>,
                Then<BitVecVectorStackView<(CallFrame<'a,V>,Frame<'a,V>)>,
                     FstView<CallFrame<'a,V>,Frame<'a,V>>>>>;

#[derive(Clone,PartialEq,Eq)]
pub enum FrameView<'a,V : 'a> {
    Call(Then<CallStackView<'a,V>,
              Then<AssocView<CallId<'a>,
                             BitVecVectorStack<(CallFrame<'a,V>,Frame<'a,V>)>>,
                   Then<BitVecVectorStackView<(CallFrame<'a,V>,Frame<'a,V>)>,
                        SndView<CallFrame<'a,V>,Frame<'a,V>>>>>),
    Stack(Then<StackView<'a,V>,
               Then<AssocView<InstructionRef<'a>,
                              BitVecVectorStack<Frame<'a,V>>>,
                    BitVecVectorStackView<Frame<'a,V>>>>)
}

pub fn frame_view_to_idx<'a,V,Em : Embed>(view: &FrameView<'a,V>,bw: usize,em: &mut Em)
                                          -> Result<(FrameId<'a>,Transf<Em>),Em::Error> {
    match view {
        &FrameView::Call(Then(_,Then(ref cid,Then(ref vec,_)))) => {
            let e = em.const_bitvec(bw,BigInt::from(vec.idx))?;
            let inp = Transformation::constant(vec![e]);
            Ok((FrameId::Call(cid.key.clone()),inp))
        },
        &FrameView::Stack(Then(_,Then(ref iid,ref vec))) => {
            let e = em.const_bitvec(bw,BigInt::from(vec.idx))?;
            let inp = Transformation::constant(vec![e]);
            Ok((FrameId::Stack(iid.key.clone()),inp))
        }
    }
}

impl<'a,V> View for FrameView<'a,V>
    where V : 'a+Bytes+FromConst<'a> {

    type Viewed = Thread<'a,V>;
    type Element = Frame<'a,V>;

    fn get_el<'b>(&self,obj: &'b Self::Viewed)
                  -> &'b Self::Element where Self : 'b {
        match self {
            &FrameView::Call(ref view)
                => view.get_el(obj),
            &FrameView::Stack(ref view)
                => view.get_el(obj)
        }
    }
    fn get_el_ext<'b>(&self,obj: &'b Self::Viewed)
                      -> (usize,&'b Self::Element) where Self : 'b {
        match self {
            &FrameView::Call(ref view)
                => view.get_el_ext(obj),
            &FrameView::Stack(ref view)
                => view.get_el_ext(obj)
        }
    }
}

impl<'a,V> ViewMut for FrameView<'a,V>
    where V : 'a+Bytes+FromConst<'a> {

    fn get_el_mut<'b>(&self,obj: &'b mut Self::Viewed)
                      -> &'b mut Self::Element where Self : 'b {
        match self {
            &FrameView::Call(ref view)
                => view.get_el_mut(obj),
            &FrameView::Stack(ref view)
                => view.get_el_mut(obj)
        }
    }
    fn get_el_mut_ext<'b>(&self,obj: &'b mut Self::Viewed)
                          -> (usize,&'b mut Self::Element)
        where Self : 'b {
        match self {
            &FrameView::Call(ref view)
                => view.get_el_mut_ext(obj),
            &FrameView::Stack(ref view)
                => view.get_el_mut_ext(obj)
        }
    }
}
