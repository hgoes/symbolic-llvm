extern crate smtrs;

use self::smtrs::composite::*;
use self::smtrs::embed::{Embed};
use super::mem::{Bytes,FromConst,MemSlice};
use super::{InstructionRef};
use super::thread::CallId;
use std::marker::PhantomData;
use std::ops::Range;
use std::cmp::Ordering;
use std::hash::{Hash,Hasher};
use std::fmt;

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash,Clone,Debug)]
pub enum ContextId<'a> {
    Call(CallId<'a>),
    Stack(CallId<'a>,InstructionRef<'a>)
}

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash,Clone,Debug)]
pub enum FrameId<'a> {
    Call(CallId<'a>),
    Stack(InstructionRef<'a>)
}

pub type PrevFrame<'a> = Choice<Data<Option<ContextId<'a>>>>;

pub type Allocations<'a,V> = Assoc<InstructionRef<'a>,Vec<MemSlice<'a,V>>>;

pub type Activation<'a> = Choice<Data<InstructionRef<'a>>>;

pub type Phi<'a> = Choice<Data<(&'a String,&'a String)>>;

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub struct Frame<'a,V> {
    pub previous: PrevFrame<'a>,
    pub allocations: Allocations<'a,V>
}

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub struct CallFrame<'a,V> {
    pub values: Assoc<&'a String,V>,
    pub arguments: Vec<V>,
    pub activation: Activation<'a>,
    pub phi: Phi<'a>
}

enum CallFrameDataVarsPos {
    Values,Arguments,Phi
}

pub struct CallFrameDataVars<'a,'b : 'a,V : 'b> {
    off: usize,
    call_frame: &'a CallFrame<'b,V>,
    pos: CallFrameDataVarsPos,
    iter: Range<usize>
}

impl<'a,'b,V : Composite> Iterator for CallFrameDataVars<'a,'b,V> {
    type Item = usize;
    fn next(&mut self) -> Option<usize> {
        loop {
            match self.iter.next() {
                Some(r) => return Some(r),
                None => match self.pos {
                    CallFrameDataVarsPos::Values => {
                        self.pos = CallFrameDataVarsPos::Arguments;
                        let args_sz = self.call_frame.arguments.num_elem();
                        let acts_sz = self.call_frame.activation.num_elem();
                        self.iter = self.off..self.off+args_sz;
                        self.off+=args_sz+acts_sz;
                    },
                    CallFrameDataVarsPos::Arguments => {
                        self.pos = CallFrameDataVarsPos::Phi;
                        let phi_sz = self.call_frame.arguments.num_elem();
                        self.iter = self.off..self.off+phi_sz;
                        self.off+=phi_sz;
                    },
                    CallFrameDataVarsPos::Phi => return None
                }
            }
        }
    }
}

impl<'a,V : Composite> CallFrame<'a,V> {
    pub fn pc_vars(&self,off: usize) -> Range<usize> {
        let off_acts = off+self.values.num_elem()+
            self.arguments.num_elem();
        let sz_acts = self.activation.num_elem();
        off_acts..off_acts+sz_acts
    }
    pub fn data_vars<'b>(&'b self,off: usize) -> (usize,CallFrameDataVars<'b,'a,V>) {
        let vals_sz = self.values.num_elem();
        let args_sz = self.arguments.num_elem();
        let acts_sz = self.activation.num_elem();
        let phi_sz = self.activation.num_elem();
        (vals_sz+args_sz+acts_sz+phi_sz,
         CallFrameDataVars { off: off+vals_sz,
                             call_frame: self,
                             pos: CallFrameDataVarsPos::Values,
                             iter: off..off+vals_sz })
    }
}

impl<'a,V : Bytes+FromConst<'a>> Frame<'a,V> {
    pub fn pc_vars(&self,off: usize) -> Range<usize> {
        off..off+self.previous.num_elem()
    }
    pub fn data_vars(&self,off: usize) -> (usize,Range<usize>) {
        let prev_sz = self.previous.num_elem();
        let alloc_sz = self.allocations.num_elem();
        (prev_sz+alloc_sz,off+prev_sz..off+prev_sz+alloc_sz)
    }
}

pub fn frame<'a,'b,'c,V,Em>(prev: OptRef<'a,PrevFrame<'b>>,
                            inp_prev: Transf<Em>,
                            alloc: OptRef<'a,Allocations<'b,V>>,
                            inp_alloc: Transf<Em>)
                            -> (OptRef<'c,Frame<'b,V>>,Transf<Em>)
    where V : Bytes+FromConst<'b>+Clone,Em : Embed {
    debug_assert_eq!(prev.as_ref().num_elem(),inp_prev.size());
    debug_assert_eq!(alloc.as_ref().num_elem(),inp_alloc.size());
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
    where V : Bytes+FromConst<'b>+Clone,Em : Embed {
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
                                 phi: OptRef<'a,Phi<'b>>,
                                 inp_phi: Transf<Em>)
                                 -> (OptRef<'c,CallFrame<'b,V>>,Transf<Em>)
    where V : Bytes+FromConst<'b>+Clone,Em : Embed {
    debug_assert_eq!(vals.as_ref().num_elem(),inp_vals.size());
    debug_assert_eq!(args.as_ref().num_elem(),inp_args.size());
    debug_assert_eq!(acts.as_ref().num_elem(),inp_acts.size());
    debug_assert_eq!(phi.as_ref().num_elem(),inp_phi.size());
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
                                           OptRef<'a,Phi<'b>>,
                                           Transf<Em>)
    where V : FromConst<'b>+Clone,Em : Embed {
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
                                         -> (OptRef<'a,Assoc<InstructionRef<'b>,Vec<MemSlice<'b,V>>>>,
                                             Transf<Em>)
    where V : Bytes+FromConst<'b>+Clone,Em : Embed {
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
    where V : Bytes+FromConst<'b>+Clone, Em : Embed {
    let sz = cf.as_ref().values.num_elem();
    let vals = match cf {
        OptRef::Ref(ref rcf) => OptRef::Ref(&rcf.values),
        OptRef::Owned(rcf) => OptRef::Owned(rcf.values)
    };
    let vals_inp = Transformation::view(0,sz,cf_inp);
    (vals,vals_inp)
}
                                         

impl<'b,V : Bytes+FromConst<'b>+Clone> Composite for Frame<'b,V> {
    fn num_elem(&self) -> usize {
        self.previous.num_elem() +
            self.allocations.num_elem()
    }
    fn elem_sort<Em : Embed>(&self,pos: usize,em: &mut Em)
                              -> Result<Em::Sort,Em::Error> {
        let sz1 = self.previous.num_elem();
        if pos < sz1 {
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

impl<'b,V : Composite+FromConst<'b>+Clone> Composite for CallFrame<'b,V> {
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

#[derive(Clone,PartialEq,Eq,Debug)]
pub struct PrevFrameView<'a,V : 'a>(PhantomData<&'a V>);

#[derive(Clone,PartialEq,Eq,Debug)]
pub struct AllocationsView<'a,V : 'a>(PhantomData<&'a V>);

#[derive(PartialEq,Eq,Debug)]
pub struct ValuesView<'a,V : 'a>(PhantomData<&'a V>);

#[derive(PartialEq,Eq,Debug)]
pub struct ArgumentsView<'a,V : 'a>(PhantomData<&'a V>);

#[derive(PartialEq,Eq,Debug)]
pub struct ActivationView<'a,V : 'a>(PhantomData<&'a V>);

#[derive(PartialEq,Eq,Debug)]
pub struct PhiView<'a,V : 'a>(PhantomData<&'a V>);

impl<'a,V> PrevFrameView<'a,V> {
    pub fn new() -> Self {
        PrevFrameView(PhantomData)
    }
}

impl<'a,V> AllocationsView<'a,V> {
    pub fn new() -> Self {
        AllocationsView(PhantomData)
    }
}

impl<'a,V> ValuesView<'a,V> {
    pub fn new() -> Self {
        ValuesView(PhantomData)
    }
}

impl<'a,V> ArgumentsView<'a,V> {
    pub fn new() -> Self {
        ArgumentsView(PhantomData)
    }
}

impl<'a,V> ActivationView<'a,V> {
    pub fn new() -> Self {
        ActivationView(PhantomData)
    }
}

impl<'a,V> PhiView<'a,V> {
    pub fn new() -> Self {
        PhiView(PhantomData)
    }
}

impl<'a,V> Clone for ValuesView<'a,V> {
    fn clone(&self) -> Self {
        ValuesView(PhantomData)
    }
}

impl<'a,V> Clone for ArgumentsView<'a,V> {
    fn clone(&self) -> Self {
        ArgumentsView(PhantomData)
    }
}

impl<'a,V> Clone for ActivationView<'a,V> {
    fn clone(&self) -> Self {
        ActivationView(PhantomData)
    }
}

impl<'a,V> Clone for PhiView<'a,V> {
    fn clone(&self) -> Self {
        PhiView(PhantomData)
    }
}

impl<'a,V> View for PrevFrameView<'a,V>
    where V : 'a + Bytes+FromConst<'a> {
    type Viewed = Frame<'a,V>;
    type Element = PrevFrame<'a>;
    fn get_el<'b>(&self,obj: &'b Self::Viewed)
                  -> &'b Self::Element where Self : 'b {
        &obj.previous
    }
    fn get_el_ext<'b>(&self,obj: &'b Self::Viewed)
                      -> (usize,&'b Self::Element) where Self : 'b {
        (0,&obj.previous)
    }
}

impl<'a,V> ViewMut for PrevFrameView<'a,V>
    where V : 'a + Bytes+FromConst<'a> {
    fn get_el_mut<'b>(&self,obj: &'b mut Self::Viewed)
                      -> &'b mut Self::Element where Self : 'b {
        &mut obj.previous
    }
    fn get_el_mut_ext<'b>(&self,obj: &'b mut Self::Viewed)
                          -> (usize,&'b mut Self::Element)
        where Self : 'b {
        (0,&mut obj.previous)
    }
}

impl<'a,V> View for AllocationsView<'a,V>
    where V : 'a + Bytes+FromConst<'a> {
    type Viewed = Frame<'a,V>;
    type Element = Allocations<'a,V>;
    fn get_el<'b>(&self,obj: &'b Self::Viewed)
                  -> &'b Self::Element where Self : 'b {
        &obj.allocations
    }
    fn get_el_ext<'b>(&self,obj: &'b Self::Viewed)
                      -> (usize,&'b Self::Element) where Self : 'b {
        (obj.previous.num_elem(),&obj.allocations)
    }
}

impl<'a,V> ViewMut for AllocationsView<'a,V>
    where V : 'a + Bytes+FromConst<'a> {
    fn get_el_mut<'b>(&self,obj: &'b mut Self::Viewed)
                      -> &'b mut Self::Element where Self : 'b {
        &mut obj.allocations
    }
    fn get_el_mut_ext<'b>(&self,obj: &'b mut Self::Viewed)
                          -> (usize,&'b mut Self::Element)
        where Self : 'b {
        (obj.previous.num_elem(),&mut obj.allocations)
    }
}

impl<'a,V> View for ValuesView<'a,V>
    where V : 'a + Bytes+FromConst<'a> {
    type Viewed = CallFrame<'a,V>;
    type Element = Assoc<&'a String,V>;
    fn get_el<'b>(&self,obj: &'b Self::Viewed)
                  -> &'b Self::Element where Self : 'b {
        &obj.values
    }
    fn get_el_ext<'b>(&self,obj: &'b Self::Viewed)
                      -> (usize,&'b Self::Element) where Self : 'b {
        (0,&obj.values)
    }
}

impl<'a,V> ViewMut for ValuesView<'a,V>
    where V : 'a + Bytes+FromConst<'a> {
    fn get_el_mut<'b>(&self,obj: &'b mut Self::Viewed)
                      -> &'b mut Self::Element where Self : 'b {
        &mut obj.values
    }
    fn get_el_mut_ext<'b>(&self,obj: &'b mut Self::Viewed)
                          -> (usize,&'b mut Self::Element)
        where Self : 'b {
        (0,&mut obj.values)
    }
}

impl<'a,V> View for ArgumentsView<'a,V>
    where V : 'a + Bytes+FromConst<'a> {
    type Viewed = CallFrame<'a,V>;
    type Element = Vec<V>;
    fn get_el<'b>(&self,obj: &'b Self::Viewed)
                  -> &'b Self::Element where Self : 'b {
        &obj.arguments
    }
    fn get_el_ext<'b>(&self,obj: &'b Self::Viewed)
                      -> (usize,&'b Self::Element) where Self : 'b {
        (obj.values.num_elem(),&obj.arguments)
    }
}

impl<'a,V> ViewMut for ArgumentsView<'a,V>
    where V : 'a + Bytes+FromConst<'a> {
    fn get_el_mut<'b>(&self,obj: &'b mut Self::Viewed)
                      -> &'b mut Self::Element where Self : 'b {
        &mut obj.arguments
    }
    fn get_el_mut_ext<'b>(&self,obj: &'b mut Self::Viewed)
                          -> (usize,&'b mut Self::Element)
        where Self : 'b {
        (obj.values.num_elem(),&mut obj.arguments)
    }
}

impl<'a,V> View for ActivationView<'a,V>
    where V : 'a + Bytes+FromConst<'a> {
    type Viewed = CallFrame<'a,V>;
    type Element = Activation<'a>;
    fn get_el<'b>(&self,obj: &'b Self::Viewed)
                  -> &'b Self::Element where Self : 'b {
        &obj.activation
    }
    fn get_el_ext<'b>(&self,obj: &'b Self::Viewed)
                      -> (usize,&'b Self::Element) where Self : 'b {
        (obj.values.num_elem()+
         obj.arguments.num_elem(),&obj.activation)
    }
}

impl<'a,V> ViewMut for ActivationView<'a,V>
    where V : 'a + Bytes+FromConst<'a> {
    fn get_el_mut<'b>(&self,obj: &'b mut Self::Viewed)
                      -> &'b mut Self::Element where Self : 'b {
        &mut obj.activation
    }
    fn get_el_mut_ext<'b>(&self,obj: &'b mut Self::Viewed)
                          -> (usize,&'b mut Self::Element)
        where Self : 'b {
        (obj.values.num_elem()+
         obj.arguments.num_elem(),&mut obj.activation)
    }
}

impl<'a,V> View for PhiView<'a,V>
    where V : 'a + Bytes+FromConst<'a> {
    type Viewed = CallFrame<'a,V>;
    type Element = Phi<'a>;
    fn get_el<'b>(&self,obj: &'b Self::Viewed)
                  -> &'b Self::Element where Self : 'b {
        &obj.phi
    }
    fn get_el_ext<'b>(&self,obj: &'b Self::Viewed)
                      -> (usize,&'b Self::Element) where Self : 'b {
        (obj.values.num_elem()+
         obj.arguments.num_elem()+
         obj.activation.num_elem(),&obj.phi)
    }
}

impl<'a,V> ViewMut for PhiView<'a,V>
    where V : 'a + Bytes+FromConst<'a> {
    fn get_el_mut<'b>(&self,obj: &'b mut Self::Viewed)
                      -> &'b mut Self::Element where Self : 'b {
        &mut obj.phi
    }
    fn get_el_mut_ext<'b>(&self,obj: &'b mut Self::Viewed)
                          -> (usize,&'b mut Self::Element)
        where Self : 'b {
        (obj.values.num_elem()+
         obj.arguments.num_elem()+
         obj.activation.num_elem(),&mut obj.phi)
    }
}

pub enum FrameMeaning<'b,V : Semantic+Bytes+FromConst<'b>> {
    Previous(<PrevFrame<'b> as Semantic>::Meaning),
    Allocations(<Allocations<'b,V> as Semantic>::Meaning)
}

impl<'b,V : Semantic+Bytes+FromConst<'b>> PartialEq for FrameMeaning<'b,V> {
    fn eq(&self,other: &FrameMeaning<'b,V>) -> bool {
        match self {
            &FrameMeaning::Previous(ref p) => match other {
                &FrameMeaning::Previous(ref q) => p.eq(q),
                _ => false
            },
            &FrameMeaning::Allocations(ref p) => match other {
                &FrameMeaning::Allocations(ref q) => p.eq(q),
                _ => false
            }
        }
    }
}

impl<'b,V : Semantic+Bytes+FromConst<'b>> Eq for FrameMeaning<'b,V> {}

impl<'b,V : Semantic+Bytes+FromConst<'b>> PartialOrd for FrameMeaning<'b,V> {
    fn partial_cmp(&self,other: &FrameMeaning<'b,V>) -> Option<Ordering> {
        match (self,other) {
            (&FrameMeaning::Previous(ref p),
             &FrameMeaning::Previous(ref q)) => p.partial_cmp(q),
            (&FrameMeaning::Previous(ref p),_) => Some(Ordering::Less),
            (&FrameMeaning::Allocations(ref p),
             &FrameMeaning::Allocations(ref q)) => p.partial_cmp(q),
            _ => Some(Ordering::Greater)
        }
    }
}

impl<'b,V : Semantic+Bytes+FromConst<'b>> Ord for FrameMeaning<'b,V> {
    fn cmp(&self,other: &FrameMeaning<'b,V>) -> Ordering {
        match (self,other) {
            (&FrameMeaning::Previous(ref p),
             &FrameMeaning::Previous(ref q)) => p.cmp(q),
            (&FrameMeaning::Previous(ref p),_) => Ordering::Less,
            (&FrameMeaning::Allocations(ref p),
             &FrameMeaning::Allocations(ref q)) => p.cmp(q),
            _ => Ordering::Greater
        }
    }
}

impl<'b,V : Semantic+Bytes+FromConst<'b>> Hash for FrameMeaning<'b,V> {
    fn hash<H>(&self, state: &mut H) where H: Hasher {
        match self {
            &FrameMeaning::Previous(ref p) => {
                (0 as u8).hash(state);
                p.hash(state);
            },
            &FrameMeaning::Allocations(ref p) => {
                (1 as u8).hash(state);
                p.hash(state);
            }
        }
    }
}

impl<'b,V : Semantic+Bytes+FromConst<'b>> fmt::Debug for FrameMeaning<'b,V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            &FrameMeaning::Previous(ref p) => f.debug_tuple("Previous")
                .field(p).finish(),
            &FrameMeaning::Allocations(ref p) => f.debug_tuple("Allocations")
                .field(p).finish()
        }
    }
}

pub enum FrameMeanings<'a,'b : 'a,V : 'a+Semantics<'a>+Bytes+FromConst<'b>> {
    Previous(<PrevFrame<'b> as Semantics<'a>>::Meanings,&'a Allocations<'b,V>),
    Allocations(<Allocations<'b,V> as Semantics<'a>>::Meanings)
}

impl<'b,V : Semantic+Bytes+FromConst<'b>> FrameMeaning<'b,V> {
    pub fn is_pc(&self) -> bool {
        match self {
            &FrameMeaning::Previous(_) => true,
            &FrameMeaning::Allocations(_) => false
        }
    }
}

impl<'a,'b : 'a,V : 'a+Semantics<'a>+Bytes+FromConst<'b>> Iterator for FrameMeanings<'a,'b,V> {
    type Item = FrameMeaning<'b,V>;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            *self = match self {
                &mut FrameMeanings::Previous(ref mut it,ref allocs) => match it.next() {
                    Some(r) => return Some(FrameMeaning::Previous(r)),
                    None => FrameMeanings::Allocations(allocs.meanings())
                },
                &mut FrameMeanings::Allocations(ref mut it) => match it.next() {
                    Some(r) => return Some(FrameMeaning::Allocations(r)),
                    None => return None
                }
            }
        }
    }
}

impl<'b,V : Semantic+Bytes+FromConst<'b>> Semantic for Frame<'b,V> {
    type Meaning = FrameMeaning<'b,V>;
    fn meaning(&self,n: usize) -> Self::Meaning {
        let sz1 = self.previous.num_elem();
        if n < sz1 {
            return FrameMeaning::Previous(self.previous.meaning(n))
        }
        FrameMeaning::Allocations(self.allocations.meaning(n-sz1))
    }
    fn fmt_meaning<F : fmt::Write>(&self,m: &Self::Meaning,fmt: &mut F) -> Result<(),fmt::Error> {
        match m {
            &FrameMeaning::Previous(ref nm) => {
                write!(fmt,"prev.")?;
                self.previous.fmt_meaning(nm,fmt)
            },
            &FrameMeaning::Allocations(ref nm) => {
                write!(fmt,"alloc.")?;
                self.allocations.fmt_meaning(nm,fmt)
            }
        }
    }
}

impl<'a,'b : 'a,V : 'a+Semantics<'a>+Bytes+FromConst<'b>> Semantics<'a> for Frame<'b,V> {
    type Meanings = FrameMeanings<'a,'b,V>;
    fn meanings(&'a self) -> Self::Meanings {
        FrameMeanings::Previous(self.previous.meanings(),&self.allocations)
    }
}

pub enum CallFrameMeaning<'b,V : Semantic> {
    Values(<Assoc<&'b String,V> as Semantic>::Meaning),
    Arguments(<Vec<V> as Semantic>::Meaning),
    Activation(<Activation<'b> as Semantic>::Meaning),
    Phi(<Choice<Data<&'b String>> as Semantic>::Meaning)
}

impl<'b,V : Semantic> PartialEq for CallFrameMeaning<'b,V> {
    fn eq(&self,other: &CallFrameMeaning<'b,V>) -> bool {
        match self {
            &CallFrameMeaning::Values(ref p) => match other {
                &CallFrameMeaning::Values(ref q) => p.eq(q),
                _ => false
            },
            &CallFrameMeaning::Arguments(ref p) => match other {
                &CallFrameMeaning::Arguments(ref q) => p.eq(q),
                _ => false
            },
            &CallFrameMeaning::Activation(ref p) => match other {
                &CallFrameMeaning::Activation(ref q) => p.eq(q),
                _ => false
            },
            &CallFrameMeaning::Phi(ref p) => match other {
                &CallFrameMeaning::Phi(ref q) => p.eq(q),
                _ => false
            },
        }
    }
}

impl<'b,V : Semantic> Eq for CallFrameMeaning<'b,V> {}

impl<'b,V : Semantic> PartialOrd for CallFrameMeaning<'b,V> {
    fn partial_cmp(&self,other: &CallFrameMeaning<'b,V>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<'b,V : Semantic> Ord for CallFrameMeaning<'b,V> {
    fn cmp(&self,other: &CallFrameMeaning<'b,V>) -> Ordering {
        match (self,other) {
            (&CallFrameMeaning::Values(ref p),
             &CallFrameMeaning::Values(ref q)) => p.cmp(q),
            (&CallFrameMeaning::Values(_),_) => Ordering::Less,
            (_,&CallFrameMeaning::Values(_)) => Ordering::Greater,
            (&CallFrameMeaning::Arguments(ref p),
             &CallFrameMeaning::Arguments(ref q)) => p.cmp(q),
            (&CallFrameMeaning::Arguments(_),_) => Ordering::Less,
            (_,&CallFrameMeaning::Arguments(_)) => Ordering::Greater,
            (&CallFrameMeaning::Activation(ref p),
             &CallFrameMeaning::Activation(ref q)) => p.cmp(q),
            (&CallFrameMeaning::Activation(_),_) => Ordering::Less,
            (_,&CallFrameMeaning::Activation(_)) => Ordering::Greater,
            (&CallFrameMeaning::Phi(ref p),
             &CallFrameMeaning::Phi(ref q)) => p.cmp(q)
        }
    }
}

impl<'b,V : Semantic> Hash for CallFrameMeaning<'b,V> {
    fn hash<H>(&self, state: &mut H) where H: Hasher {
        match self {
            &CallFrameMeaning::Values(ref p) => {
                (0 as u8).hash(state);
                p.hash(state);
            },
            &CallFrameMeaning::Arguments(ref p) => {
                (1 as u8).hash(state);
                p.hash(state);
            },
            &CallFrameMeaning::Activation(ref p) => {
                (2 as u8).hash(state);
                p.hash(state);
            },
            &CallFrameMeaning::Phi(ref p) => {
                (3 as u8).hash(state);
                p.hash(state);
            }
        }
    }
}

impl<'b,V : Semantic> fmt::Debug for CallFrameMeaning<'b,V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            &CallFrameMeaning::Values(ref p) => f.debug_tuple("Values")
                .field(p).finish(),
            &CallFrameMeaning::Arguments(ref p) => f.debug_tuple("Arguments")
                .field(p).finish(),
            &CallFrameMeaning::Activation(ref p) => f.debug_tuple("Activation")
                .field(p).finish(),
            &CallFrameMeaning::Phi(ref p) => f.debug_tuple("Phi")
                .field(p).finish()
        }
    }
}

pub enum CallFrameMeanings<'a,'b : 'a,V : 'a+Semantics<'a>> {
    Values(<Assoc<&'b String,V> as Semantics<'a>>::Meanings,&'a CallFrame<'b,V>),
    Arguments(<Vec<V> as Semantics<'a>>::Meanings,&'a CallFrame<'b,V>),
    Activation(<Activation<'b> as Semantics<'a>>::Meanings,&'a CallFrame<'b,V>),
    Phi(<Phi<'b> as Semantics<'a>>::Meanings)
}

impl<'b,V : Semantic> CallFrameMeaning<'b,V> {
    pub fn is_pc(&self) -> bool {
        match self {
            &CallFrameMeaning::Activation(_) => true,
            &CallFrameMeaning::Phi(_) => true,
            _ => false
        }
    }
}

impl<'a,'b : 'a,V : 'a+Semantics<'a>> Iterator for CallFrameMeanings<'a,'b,V> {
    type Item = CallFrameMeaning<'b,V>;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            *self = match self {
                &mut CallFrameMeanings::Values(ref mut it,cf) => match it.next() {
                    Some(r) => return Some(CallFrameMeaning::Values(r)),
                    None => CallFrameMeanings::Arguments(cf.arguments.meanings(),cf)
                },
                &mut CallFrameMeanings::Arguments(ref mut it,cf) => match it.next() {
                    Some(r) => return Some(CallFrameMeaning::Arguments(r)),
                    None => CallFrameMeanings::Activation(cf.activation.meanings(),cf)
                },
                &mut CallFrameMeanings::Activation(ref mut it,cf) => match it.next() {
                    Some(r) => return Some(CallFrameMeaning::Activation(r)),
                    None => CallFrameMeanings::Phi(cf.phi.meanings())
                },
                &mut CallFrameMeanings::Phi(ref mut it) => match it.next() {
                    Some(r) => return Some(CallFrameMeaning::Phi(r)),
                    None => return None
                }
            }
        }
    }
}

impl<'b,V : Semantic+Bytes+FromConst<'b>> Semantic for CallFrame<'b,V> {
    type Meaning = CallFrameMeaning<'b,V>;
    fn meaning(&self,pos: usize) -> Self::Meaning {
        let off1 = self.values.num_elem();
        if pos < off1 {
            return CallFrameMeaning::Values(self.values.meaning(pos))
        }
        let off2 = off1+self.arguments.num_elem();
        if pos < off2 {
            return CallFrameMeaning::Arguments(self.arguments.meaning(pos-off1))
        }
        let off3 = off2+self.activation.num_elem();
        if pos < off3 {
            return CallFrameMeaning::Activation(self.activation.meaning(pos-off2))
        }
        CallFrameMeaning::Phi(self.phi.meaning(pos-off3))
    }
    fn fmt_meaning<F : fmt::Write>(&self,m: &Self::Meaning,fmt: &mut F) -> Result<(),fmt::Error> {
        match m {
            &CallFrameMeaning::Values(ref nm) => {
                write!(fmt,"values.")?;
                self.values.fmt_meaning(nm,fmt)
            },
            &CallFrameMeaning::Arguments(ref nm) => {
                write!(fmt,"args.")?;
                self.arguments.fmt_meaning(nm,fmt)
            },
            &CallFrameMeaning::Activation(ref nm) => {
                write!(fmt,"act.")?;
                self.activation.fmt_meaning(nm,fmt)
            },
            &CallFrameMeaning::Phi(ref nm) => {
                write!(fmt,"phi.")?;
                self.phi.fmt_meaning(nm,fmt)
            }
        }
    }
}

impl<'a,'b : 'a,V : 'a+Semantics<'a>+Bytes+FromConst<'b>> Semantics<'a> for CallFrame<'b,V> {
    type Meanings = CallFrameMeanings<'a,'b,V>;
    fn meanings(&'a self) -> Self::Meanings {
        CallFrameMeanings::Values(self.values.meanings(),self)
    }
}
