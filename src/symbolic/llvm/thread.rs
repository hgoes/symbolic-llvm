extern crate smtrs;

use self::smtrs::composite::*;
use self::smtrs::embed::{Embed,DeriveConst,DeriveValues};
use self::smtrs::domain::{Domain};
use super::mem::{Bytes};
use super::frame::{CallFrame,Frame,FrameId};
use super::{InstructionRef};
use std::fmt::Debug;

pub type CallId<'a> = (Option<InstructionRef<'a>>,&'a String);

pub type CallStack<'a,V> = Assoc<CallId<'a>,
                                 BitVecVectorStack<(CallFrame<'a,V>,Frame<'a,V>)>>;
pub type Stack<'a,V> = Assoc<InstructionRef<'a>,
                             BitVecVectorStack<Frame<'a,V>>>;
pub type StackTop<'a> = Choice<Data<Option<FrameId<'a>>>>;

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub struct Thread<'a,V : Bytes + Clone> {
    call_stack: CallStack<'a,V>,
    stack: Stack<'a,V>,
    stack_top: StackTop<'a>,
    ret: Option<V>
}

pub fn get_top_call_frame<'a,'b,V,Em>(cfs: OptRef<'a,CallStack<'b,V>>,
                                      cfs_inp: Transf<Em>,
                                      cf_id: &CallId<'b>,
                                      exprs: &[Em::Expr],
                                      em: &mut Em)
                                      -> Result<Option<(OptRef<'a,CallFrame<'b,V>>,Transf<Em>)>,Em::Error>
    where V : Bytes+Clone,Em : DeriveConst {
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
                                          em: &mut Em)
                                          -> Result<Transf<Em>,Em::Error>
    where Em : Embed {
    let mut res = Vec::new();
    for (ref el,ref cond,_) in top.as_ref().choices(top_inp) {
        let same_cf = match el.0 {
            None => false,
            Some(ref fr_id) => match fr_id {
                &FrameId::Call(ref id) => *id==*cf_id,
                &FrameId::Stack(ref id,_) => *id==*cf_id
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
    where V : Bytes+Clone,Em : Embed {
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
    where V : Bytes+Clone,Em : Embed {
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
                                    -> (OptRef<'a,Choice<Data<Option<FrameId<'b>>>>>,
                                        Transf<Em>)
    where V : Bytes+Clone,Em : Embed {
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
    where V : Bytes+Clone,Em : DeriveConst {

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
        &FrameId::Stack(ref cs_id,ref st_id) => {
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
    where V : Bytes+Clone,Em : Embed {
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
    where V : Bytes + Clone,Em : Embed {
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

impl<'b,V : Bytes + Clone> Composite for Thread<'b,V> {
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
