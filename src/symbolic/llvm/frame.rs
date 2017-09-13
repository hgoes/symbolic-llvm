extern crate smtrs;

use self::smtrs::composite::*;
use self::smtrs::embed::{Embed};
use super::mem::{Bytes,MemSlice};
use super::{InstructionRef};
use super::thread::CallId;

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash,Clone)]
pub enum FrameId<'a> {
    Call(CallId<'a>),
    Stack(CallId<'a>,InstructionRef<'a>)
}

pub type PrevFrame<'a> = Choice<Option<Data<FrameId<'a>>>>;

pub type Allocations<'a,V> = Assoc<InstructionRef<'a>,Vec<MemSlice<V>>>;

pub type Activation<'a> = Choice<Data<InstructionRef<'a>>>;

#[derive(PartialEq,Eq,Hash,Clone)]
pub struct Frame<'a,V : Bytes + Clone> {
    previous: PrevFrame<'a>,
    allocations: Allocations<'a,V>
}

#[derive(PartialEq,Eq,Hash,Clone)]
pub struct CallFrame<'a,V> {
    values: Assoc<&'a String,V>,
    arguments: Vec<V>,
    activation: Activation<'a>,
    phi: Choice<Data<&'a String>>
}

pub fn frame<'a,'b,'c,V,Em>(prev: OptRef<'a,PrevFrame<'b>>,
                            inp_prev: Transf<Em>,
                            alloc: OptRef<'a,Allocations<'b,V>>,
                            inp_alloc: Transf<Em>)
                            -> (OptRef<'c,Frame<'b,V>>,Transf<Em>)
    where V : Bytes + Clone,Em : Embed {
    (OptRef::Owned(Frame { previous: prev.as_obj(),
                           allocations: alloc.as_obj() }),
     Transformation::concat(&[inp_prev,inp_alloc]))
}
                         

pub fn decompose_frame<'a,'b,V,Em>(fr: OptRef<'a,Frame<'b,V>>,
                                   inp_fr: Transf<Em>)
                                   -> (OptRef<'a,PrevFrame<'b>>,
                                       Transf<Em>,
                                       OptRef<'a,Allocations<'b,V>>,
                                       Transf<Em>)
    where V : Bytes + Clone,Em : Embed {
    let (prev,alloc) = match fr {
        OptRef::Ref(ref rx) => (OptRef::Ref(&rx.previous),
                                OptRef::Ref(&rx.allocations)),
        OptRef::Owned(rx) => (OptRef::Owned(rx.previous),
                              OptRef::Owned(rx.allocations))
    };
    let sz_prev = prev.as_ref().num_elem();
    let sz_alloc = alloc.as_ref().num_elem();
    let inp_prev = Transformation::view(0,sz_prev,inp_fr.clone());
    let inp_alloc = Transformation::view(sz_prev,sz_alloc,inp_fr);
    (prev,inp_prev,alloc,inp_alloc)
}

pub fn call_frame<'a,'b,'c,V,Em>(vals: OptRef<'a,Assoc<&'b String,V>>,
                                 inp_vals: Transf<Em>,
                                 args: OptRef<'a,Vec<V>>,
                                 inp_args: Transf<Em>,
                                 acts: OptRef<'a,Activation<'b>>,
                                 inp_acts: Transf<Em>,
                                 phi: OptRef<'a,Choice<Data<&'b String>>>,
                                 inp_phi: Transf<Em>)
                                 -> (OptRef<'c,CallFrame<'b,V>>,Transf<Em>)
    where V : Bytes+Clone,Em : Embed {
    (OptRef::Owned(CallFrame { values: vals.as_obj(),
                               arguments: args.as_obj(),
                               activation: acts.as_obj(),
                               phi: phi.as_obj() }),
     Transformation::concat(&[inp_vals,inp_args,inp_acts,inp_phi]))
}
    

pub fn decompose_callframe<'a,'b,V,Em>(cf: OptRef<'a,CallFrame<'b,V>>,inp_cf: Transf<Em>)
                                       -> (OptRef<'a,Assoc<&'b String,V>>,
                                           Transf<Em>,
                                           OptRef<'a,Vec<V>>,
                                           Transf<Em>,
                                           OptRef<'a,Activation<'b>>,
                                           Transf<Em>,
                                           OptRef<'a,Choice<Data<&'b String>>>,
                                           Transf<Em>)
    where V : Composite+Clone,Em : Embed {
    let (vals,args,acts,phi) = match cf {
        OptRef::Ref(ref cf)
            => (OptRef::Ref(&cf.values),
                OptRef::Ref(&cf.arguments),
                OptRef::Ref(&cf.activation),
                OptRef::Ref(&cf.phi)),
        OptRef::Owned(cf)
            => (OptRef::Owned(cf.values),
                OptRef::Owned(cf.arguments),
                OptRef::Owned(cf.activation),
                OptRef::Owned(cf.phi))
    };
    let sz_vals = vals.as_ref().num_elem();
    let inp_vals = Transformation::view(0,sz_vals,inp_cf.clone());
    let sz_args = args.as_ref().num_elem();
    let inp_args = Transformation::view(sz_vals,sz_args,inp_cf.clone());
    let sz_acts = acts.as_ref().num_elem();
    let inp_acts = Transformation::view(sz_vals+sz_args,sz_acts,inp_cf.clone());
    let sz_phi = phi.as_ref().num_elem();
    let inp_phi = Transformation::view(sz_vals+sz_args+sz_acts,sz_phi,inp_cf);
    (vals,inp_vals,
     args,inp_args,
     acts,inp_acts,
     phi,inp_phi)
}

pub fn frame_get_allocations<'a,'b,V,Em>(frame: OptRef<'a,Frame<'b,V>>,
                                     frame_inp: Transf<Em>)
                                     -> (OptRef<'a,Assoc<InstructionRef<'a>,Vec<MemSlice<V>>>>,
                                         Transf<Em>)
    where V : Bytes+Clone,Em : Embed {
    let off = frame.as_ref().previous.num_elem();
    let sz = frame.as_ref().allocations.num_elem();
    let alloc = match frame {
        OptRef::Ref(ref rframe) => OptRef::Ref(&rframe.allocations),
        OptRef::Owned(rframe) => OptRef::Owned(rframe.allocations)
    };
    let alloc_inp = Transformation::view(off,sz,frame_inp);
    (alloc,alloc_inp)
}

pub fn call_frame_get_values<'a,'b,V,Em>(cf: OptRef<'a,CallFrame<'b,V>>,
                                         cf_inp: Transf<Em>)
                                         -> (OptRef<'a,Assoc<&'b String,V>>,
                                             Transf<Em>)
    where V : Bytes + Clone, Em : Embed {
    let sz = cf.as_ref().values.num_elem();
    let vals = match cf {
        OptRef::Ref(ref rcf) => OptRef::Ref(&rcf.values),
        OptRef::Owned(rcf) => OptRef::Owned(rcf.values)
    };
    let vals_inp = Transformation::view(0,sz,cf_inp);
    (vals,vals_inp)
}
                                         

impl<'b,V : Bytes + Clone> Composite for Frame<'b,V> {
    fn num_elem(&self) -> usize {
        self.previous.num_elem() +
            self.allocations.num_elem()
    }
    fn elem_sort<Em : Embed>(&self,pos: usize,em: &mut Em)
                              -> Result<Em::Sort,Em::Error> {
        let sz1 = self.previous.num_elem();
        if pos >= sz1 {
            return self.previous.elem_sort(pos,em)
        }
        return self.allocations.elem_sort(pos-sz1,em)
    }
    fn combine<'a,Em,FComb,FL,FR>(x: OptRef<'a,Self>,y: OptRef<'a,Self>,
                                  inp_x: Transf<Em>,inp_y: Transf<Em>,
                                  comb: &FComb,only_l: &FL,only_r: &FR,em: &mut Em)
                                  -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>
        where Em : Embed,
              FComb : Fn(Transf<Em>,Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FL : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FR : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error> {

        let (prev_x,inp_prev_x,alloc_x,inp_alloc_x) = decompose_frame(x,inp_x);
        let (prev_y,inp_prev_y,alloc_y,inp_alloc_y) = decompose_frame(y,inp_y);
        
        match Choice::combine(prev_x,prev_y,
                              inp_prev_x,inp_prev_y,
                              comb,only_l,only_r,em)? {
            None => Ok(None),
            Some((nprev,inp_nprev)) => {
                match Assoc::combine(alloc_x,alloc_y,
                                     inp_alloc_x,inp_alloc_y,
                                     comb,only_l,only_r,em)? {
                    None => Ok(None),
                    Some((nalloc,inp_nalloc))
                        => Ok(Some((OptRef::Owned(Frame { previous: nprev.as_obj(),
                                                          allocations: nalloc.as_obj() }),
                                    Transformation::concat(&[inp_nprev,inp_nalloc]))))
                }
            }
        }
    }
}

impl<'b,V : Composite + Clone> Composite for CallFrame<'b,V> {
    fn num_elem(&self) -> usize {
        self.values.num_elem() +
            self.arguments.num_elem() +
            self.activation.num_elem() +
            self.phi.num_elem()
    }
    fn elem_sort<Em : Embed>(&self,pos: usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        let off1 = self.values.num_elem();
        if pos < off1 {
            return self.values.elem_sort(pos,em)
        }
        let off2 = off1+self.arguments.num_elem();
        if pos < off2 {
            return self.arguments.elem_sort(pos-off1,em)
        }
        let off3 = off2+self.activation.num_elem();
        if pos < off3 {
            return self.activation.elem_sort(pos-off2,em)
        }
        self.phi.elem_sort(pos-off3,em)
    }
    fn combine<'a,Em,FComb,FL,FR>(x: OptRef<'a,Self>,y: OptRef<'a,Self>,
                                  inp_x: Transf<Em>,inp_y: Transf<Em>,
                                  comb: &FComb,only_l: &FL,only_r: &FR,em: &mut Em)
                                  -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>
        where Em : Embed,
              FComb : Fn(Transf<Em>,Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FL : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FR : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error> {

        let (vals_x,inp_vals_x,args_x,inp_args_x,acts_x,inp_acts_x,phi_x,inp_phi_x) = decompose_callframe(x,inp_x);
        let (vals_y,inp_vals_y,args_y,inp_args_y,acts_y,inp_acts_y,phi_y,inp_phi_y) = decompose_callframe(y,inp_y);
        let (nvalues,nvalues_inp) = match Assoc::combine(vals_x,vals_y,
                                                         inp_vals_x,inp_vals_y,
                                                         comb,only_l,only_r,em)? {
            Some(r) => r,
            None => return Ok(None)
        };
        let (nargs,nargs_inp) = match Vec::combine(args_x,args_y,
                                                   inp_args_x,inp_args_y,
                                                   comb,only_l,only_r,em)? {
            Some(r) => r,
            None => return Ok(None)
        };
        let (nact,nact_inp) = match Choice::combine(acts_x,acts_y,
                                                    inp_acts_x,inp_acts_y,
                                                    comb,only_l,only_r,em)? {
            Some(r) => r,
            None => return Ok(None)
        };
        let (nphi,nphi_inp) = match Choice::combine(phi_x,phi_y,
                                                    inp_phi_x,inp_phi_y,
                                                    comb,only_l,only_r,em)? {
            Some(r) => r,
            None => return Ok(None)
        };
        Ok(Some((OptRef::Owned(CallFrame { values: nvalues.as_obj(),
                                           arguments: nargs.as_obj(),
                                           activation: nact.as_obj(),
                                           phi: nphi.as_obj() }),
                 Transformation::concat(&[nvalues_inp,nargs_inp,nact_inp,nphi_inp]))))
    }
}
