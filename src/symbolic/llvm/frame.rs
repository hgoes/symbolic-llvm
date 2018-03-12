use smtrs::composite::*;
use smtrs::composite::vec::*;
use smtrs::composite::choice::*;
use smtrs::composite::singleton::*;
use smtrs::composite::map::*;
use smtrs::embed::{Embed};
use super::mem::{Bytes,FromConst,MemSlice};
use super::{InstructionRef};
use super::thread::CallId;
use std::marker::PhantomData;
use std::ops::Range;
use std::cmp::Ordering;
use std::hash::{Hash,Hasher};
use std::fmt;
use std::fmt::Debug;

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

pub type Allocations<'a,V> = Assoc<InstructionRef<'a>,CompVec<MemSlice<'a,V>>>;

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
    pub arguments: CompVec<V>,
    pub activation: Activation<'a>,
    pub phi: Phi<'a>
}

impl<'a,V> Frame<'a,V> {
    pub fn construct<Em,FPrev,FAlloc>(
        fprev: FPrev,
        falloc: FAlloc,
        res: &mut Vec<Em::Expr>,
        em: &mut Em
    ) -> Result<Self,Em::Error>
        where
        Em: Embed,
        FPrev: FnOnce(&mut Vec<Em::Expr>,&mut Em)
                      -> Result<PrevFrame<'a>,Em::Error>,
        FAlloc: FnOnce(&mut Vec<Em::Expr>,&mut Em)
                       -> Result<Allocations<'a,V>,Em::Error> {
        let prev = fprev(res,em)?;
        let alloc = falloc(res,em)?;
        Ok(Frame { previous: prev,
                   allocations: alloc })
    }
    pub fn previous() -> PrevFramePath {
        PrevFramePath
    }
    pub fn allocations() -> AllocationsPath {
        AllocationsPath
    }
}

impl<'a,V> CallFrame<'a,V> {
    pub fn construct<Em,FVals,FArgs,FActs,FPhi>(
        fvals: FVals,
        fargs: FArgs,
        facts: FActs,
        fphi: FPhi,
        res: &mut Vec<Em::Expr>,
        em: &mut Em
    ) -> Result<Self,Em::Error>
        where
        Em: Embed,
        FVals: FnOnce(&mut Vec<Em::Expr>,&mut Em)
                      -> Result<Assoc<&'a String,V>,Em::Error>,
        FArgs: FnOnce(&mut Vec<Em::Expr>,&mut Em)
                      -> Result<CompVec<V>,Em::Error>,
        FActs: FnOnce(&mut Vec<Em::Expr>,&mut Em)
                      -> Result<Activation<'a>,Em::Error>,
        FPhi: FnOnce(&mut Vec<Em::Expr>,&mut Em)
                     -> Result<Phi<'a>,Em::Error> {
        let vals = fvals(res,em)?;
        let args = fargs(res,em)?;
        let acts = facts(res,em)?;
        let phi  = fphi(res,em)?;
        Ok(CallFrame { values: vals,
                       arguments: args,
                       activation: acts,
                       phi: phi })
    }
    pub fn values() -> ValuesPath {
        ValuesPath
    }
    pub fn arguments() -> ArgumentsPath {
        ArgumentsPath
    }
    pub fn activation() -> ActivationPath {
        ActivationPath
    }
    pub fn phi() -> PhiPath {
        PhiPath
    }
}

/*pub fn frame<'a,'b,'c,V,Em>(prev: OptRef<'a,PrevFrame<'b>>,
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
}*/

impl<'b,V: HasSorts> HasSorts for Frame<'b,V> {
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
}

impl<'a,V: Bytes<'a>+FromConst<'a>> Composite<'a> for Frame<'a,V> {
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

        let prev_l = then(pl.clone(),
                          PrevFramePath);
        let prev_r = then(pr.clone(),
                          PrevFramePath);
        let nprev = match PrevFrame::combine(&prev_l,froml,arrl,
                                             &prev_r,fromr,arrr,
                                             comb,only_l,only_r,
                                             res,em)? {
            None => return Ok(None),
            Some(obj) => obj
        };

        let alloc_l = then(pl.clone(),
                           AllocationsPath);
        let alloc_r = then(pr.clone(),
                           AllocationsPath);
        let nalloc = match Assoc::combine(&alloc_l,froml,arrl,
                                          &alloc_r,fromr,arrr,
                                          comb,only_l,only_r,
                                          res,em)? {
            None => return Ok(None),
            Some(obj) => obj
        };
        
        Ok(Some(Frame { previous: nprev,
                        allocations: nalloc }))
    }
}

impl<'b,V: HasSorts> HasSorts for CallFrame<'b,V> {
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
}

impl<'a,V: Composite<'a>> Composite<'a> for CallFrame<'a,V> {
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

        let vals_l = then(pl.clone(),ValuesPath);
        let vals_r = then(pr.clone(),ValuesPath);
        let nvals = match Assoc::combine(&vals_l,froml,arrl,
                                         &vals_r,fromr,arrr,
                                         comb,only_l,only_r,
                                         res,em)? {
            None => return Ok(None),
            Some(obj) => obj
        };

        let args_l = then(pl.clone(),ArgumentsPath);
        let args_r = then(pr.clone(),ArgumentsPath);
        let nargs = match CompVec::combine(&args_l,froml,arrl,
                                           &args_r,fromr,arrr,
                                           comb,only_l,only_r,
                                           res,em)? {
            None => return Ok(None),
            Some(obj) => obj
        };

        let act_l = then(pl.clone(),ActivationPath);
        let act_r = then(pr.clone(),ActivationPath);
        let nact = match Activation::combine(&act_l,froml,arrl,
                                             &act_r,fromr,arrr,
                                             comb,only_l,only_r,
                                             res,em)? {
            None => return Ok(None),
            Some(obj) => obj
        };

        let phi_l = then(pl.clone(),PhiPath);
        let phi_r = then(pr.clone(),PhiPath);
        let nphi = match Phi::combine(&phi_l,froml,arrl,
                                      &phi_r,fromr,arrr,
                                      comb,only_l,only_r,
                                      res,em)? {
            None => return Ok(None),
            Some(obj) => obj
        };

        Ok(Some(CallFrame {
            values: nvals,
            arguments: nargs,
            activation: nact,
            phi: nphi
        }))
    }
}

#[derive(Clone,PartialEq,Eq,Debug)]
pub struct PrevFramePath;

#[derive(Clone,PartialEq,Eq,Debug)]
pub struct AllocationsPath;

#[derive(Clone,PartialEq,Eq,Debug)]
pub struct ValuesPath;

#[derive(Clone,PartialEq,Eq,Debug)]
pub struct ArgumentsPath;

#[derive(Clone,PartialEq,Eq,Debug)]
pub struct ActivationPath;

#[derive(Clone,PartialEq,Eq,Debug)]
pub struct PhiPath;

impl PrevFramePath {
    pub fn new() -> Self {
        PrevFramePath
    }
}

impl AllocationsPath {
    pub fn new() -> Self {
        AllocationsPath
    }
}

impl ValuesPath {
    pub fn new() -> Self {
        ValuesPath
    }
}

impl ArgumentsPath {
    pub fn new() -> Self {
        ArgumentsPath
    }
}

impl ActivationPath {
    pub fn new() -> Self {
        ActivationPath
    }
}

impl PhiPath {
    pub fn new() -> Self {
        PhiPath
    }
}

impl<'a,V> SimplePathEl<'a,Frame<'a,V>> for PrevFramePath
    where V: 'a {
    type To = PrevFrame<'a>;
    fn get<'b>(&self,obj: &'b Frame<'a,V>)
               -> &'b Self::To where 'a: 'b {
        &obj.previous
    }
    fn get_mut<'c>(&self,from: &'c mut Frame<'a,V>)
                   -> &'c mut Self::To where 'a: 'c {
        &mut from.previous
    }
}

impl<'a,Em: Embed,V> PathEl<'a,Em,Frame<'a,V>> for PrevFramePath
    where V: 'a+HasSorts+Clone {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Frame<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        prev.read(prev_from,pos,arr,em)
    }
    fn read_slice<'c,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Frame<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        len: usize,
        arr: &'c [Em::Expr])
        -> Option<&'c [Em::Expr]> {
        prev.read_slice(prev_from,pos,len,arr)
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Frame<'a,V>>>(
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
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Frame<'a,V>>>(
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

impl<'a,V> SimplePathEl<'a,Frame<'a,V>> for AllocationsPath
    where V: 'a {
    type To   = Allocations<'a,V>;
    fn get<'c>(&self,from: &'c Frame<'a,V>) -> &'c Self::To where 'a: 'c {
        &from.allocations
    }
    fn get_mut<'c>(&self,from: &'c mut Frame<'a,V>) -> &'c mut Self::To where 'a: 'c {
        &mut from.allocations
    }
}

impl<'a,Em: Embed,V> PathEl<'a,Em,Frame<'a,V>> for AllocationsPath
    where V: 'a+HasSorts+Clone {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Frame<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        let off = prev.get(prev_from).previous.num_elem();
        prev.read(prev_from,pos+off,arr,em)
    }
    fn read_slice<'c,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Frame<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        len: usize,
        arr: &'c [Em::Expr])
        -> Option<&'c [Em::Expr]> {
        let off = prev.get(prev_from).previous.num_elem();
        prev.read_slice(prev_from,pos+off,len,arr)
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Frame<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        e: Em::Expr,
        arr: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        let off = prev.get(prev_from).previous.num_elem();
        prev.write(prev_from,pos+off,e,arr,em)
    }
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Frame<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &mut PrevFrom,
        pos: usize,
        old_len: usize,
        src: &mut Vec<Em::Expr>,
        trg: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        let off = prev.get(prev_from).previous.num_elem();
        prev.write_slice(prev_from,pos+off,old_len,src,trg,em)
    }
}

impl<'a,V> SimplePathEl<'a,CallFrame<'a,V>> for ValuesPath
    where V: 'a {
    type To = Assoc<&'a String,V>;
    fn get<'c>(&self,from: &'c CallFrame<'a,V>) -> &'c Self::To where 'a: 'c {
        &from.values
    }
    fn get_mut<'c>(&self,from: &'c mut CallFrame<'a,V>) -> &'c mut Self::To where 'a: 'c {
        &mut from.values
    }
}

impl<'a,Em: Embed,V> PathEl<'a,Em,CallFrame<'a,V>> for ValuesPath
    where V: 'a+HasSorts+Clone {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CallFrame<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        prev.read(prev_from,pos,arr,em)
    }
    fn read_slice<'c,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CallFrame<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        len: usize,
        arr: &'c [Em::Expr])
        -> Option<&'c [Em::Expr]> {
        prev.read_slice(prev_from,pos,len,arr)
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CallFrame<'a,V>>>(
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
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CallFrame<'a,V>>>(
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

impl<'a,V> SimplePathEl<'a,CallFrame<'a,V>> for ArgumentsPath
    where V: 'a {
    type To = CompVec<V>;
    fn get<'c>(&self,from: &'c CallFrame<'a,V>) -> &'c Self::To where 'a: 'c {
        &from.arguments
    }
    fn get_mut<'c>(&self,from: &'c mut CallFrame<'a,V>) -> &'c mut Self::To where 'a: 'c {
        &mut from.arguments
    }
}

impl<'a,Em: Embed,V> PathEl<'a,Em,CallFrame<'a,V>> for ArgumentsPath
    where V: 'a+HasSorts+Clone {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CallFrame<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        let off = prev.get(prev_from).values.num_elem();
        prev.read(prev_from,pos+off,arr,em)
    }
    fn read_slice<'c,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CallFrame<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        len: usize,
        arr: &'c [Em::Expr])
        -> Option<&'c [Em::Expr]> {
        let off = prev.get(prev_from).values.num_elem();
        prev.read_slice(prev_from,pos+off,len,arr)
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CallFrame<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        e: Em::Expr,
        arr: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        let off = prev.get(prev_from).values.num_elem();
        prev.write(prev_from,pos+off,e,arr,em)
    }
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CallFrame<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &mut PrevFrom,
        pos: usize,
        old_len: usize,
        src: &mut Vec<Em::Expr>,
        trg: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        let off = prev.get(prev_from).values.num_elem();
        prev.write_slice(prev_from,pos+off,old_len,src,trg,em)
    }
}

impl<'a,V> SimplePathEl<'a,CallFrame<'a,V>> for ActivationPath
    where V: 'a {
    type To   = Activation<'a>;
    fn get<'c>(&self,from: &'c CallFrame<'a,V>) -> &'c Self::To where 'a: 'c {
        &from.activation
    }
    fn get_mut<'c>(&self,from: &'c mut CallFrame<'a,V>) -> &'c mut Self::To where 'a: 'c {
        &mut from.activation
    }
}

impl<'a,Em: Embed,V> PathEl<'a,Em,CallFrame<'a,V>> for ActivationPath
    where V: 'a+HasSorts+Clone {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CallFrame<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        let off = {
            let from = prev.get(prev_from);
            from.values.num_elem() + from.arguments.num_elem()
        };
        prev.read(prev_from,pos+off,arr,em)
    }
    fn read_slice<'c,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CallFrame<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        len: usize,
        arr: &'c [Em::Expr])
        -> Option<&'c [Em::Expr]> {
        let off = {
            let from = prev.get(prev_from);
            from.values.num_elem() + from.arguments.num_elem()
        };
        prev.read_slice(prev_from,pos+off,len,arr)
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CallFrame<'a,V>>>(
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
            from.values.num_elem() + from.arguments.num_elem()
        };
        prev.write(prev_from,pos+off,e,arr,em)
    }
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CallFrame<'a,V>>>(
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
            from.values.num_elem() + from.arguments.num_elem()
        };
        prev.write_slice(prev_from,pos+off,old_len,src,trg,em)
    }
}

impl<'a,V> SimplePathEl<'a,CallFrame<'a,V>> for PhiPath
    where V: 'a {
    type To   = Phi<'a>;
    fn get<'c>(&self,from: &'c CallFrame<'a,V>) -> &'c Self::To where 'a: 'c {
        &from.phi
    }
    fn get_mut<'c>(&self,from: &'c mut CallFrame<'a,V>) -> &'c mut Self::To where 'a: 'c {
        &mut from.phi
    }
}

impl<'a,Em: Embed,V> PathEl<'a,Em,CallFrame<'a,V>> for PhiPath
    where V: 'a+HasSorts+Clone {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CallFrame<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        let off = {
            let from = prev.get(prev_from);
            from.values.num_elem()
                + from.arguments.num_elem()
                + from.activation.num_elem()
        };
        prev.read(prev_from,pos+off,arr,em)
    }
    fn read_slice<'c,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CallFrame<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        len: usize,
        arr: &'c [Em::Expr])
        -> Option<&'c [Em::Expr]> {
        let off = {
            let from = prev.get(prev_from);
            from.values.num_elem()
                + from.arguments.num_elem()
                + from.activation.num_elem()
        };
        prev.read_slice(prev_from,pos+off,len,arr)
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CallFrame<'a,V>>>(
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
            from.values.num_elem()
                + from.arguments.num_elem()
                + from.activation.num_elem()
        };
        prev.write(prev_from,pos+off,e,arr,em)
    }
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CallFrame<'a,V>>>(
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
            from.values.num_elem()
                + from.arguments.num_elem()
                + from.activation.num_elem()
        };
        prev.write_slice(prev_from,pos+off,old_len,src,trg,em)
    }
}

#[derive(Clone)]
pub enum FrameMeaning<'b,V: Semantic+Bytes<'b>+FromConst<'b>> {
    Previous(<PrevFrame<'b> as Semantic>::Meaning),
    Allocations(<Allocations<'b,V> as Semantic>::Meaning)
}

pub enum FrameMeaningCtx<'b,V: Semantic+Bytes<'b>+FromConst<'b>> {
    Previous(<PrevFrame<'b> as Semantic>::MeaningCtx),
    Allocations(<Allocations<'b,V> as Semantic>::MeaningCtx)
}

impl<'b,V : Semantic+Bytes<'b>+FromConst<'b>> PartialEq for FrameMeaning<'b,V> {
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

impl<'b,V : Semantic+Bytes<'b>+FromConst<'b>> Eq for FrameMeaning<'b,V> {}

impl<'b,V : Semantic+Bytes<'b>+FromConst<'b>> PartialOrd for FrameMeaning<'b,V> {
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

impl<'b,V : Semantic+Bytes<'b>+FromConst<'b>> Ord for FrameMeaning<'b,V> {
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

impl<'b,V : Semantic+Bytes<'b>+FromConst<'b>> Hash for FrameMeaning<'b,V> {
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

impl<'b,V : Semantic+Bytes<'b>+FromConst<'b>> fmt::Debug for FrameMeaning<'b,V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            &FrameMeaning::Previous(ref p) => f.debug_tuple("Previous")
                .field(p).finish(),
            &FrameMeaning::Allocations(ref p) => f.debug_tuple("Allocations")
                .field(p).finish()
        }
    }
}

impl<'b,V : Semantic+Bytes<'b>+FromConst<'b>> FrameMeaning<'b,V> {
    pub fn is_pc(&self) -> bool {
        match self {
            &FrameMeaning::Previous(_) => true,
            &FrameMeaning::Allocations(_) => false
        }
    }
}

impl<'b,V : Semantic+Bytes<'b>+FromConst<'b>> Semantic for Frame<'b,V> {
    type Meaning = FrameMeaning<'b,V>;
    type MeaningCtx = FrameMeaningCtx<'b,V>;
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
    fn first_meaning(&self) -> Option<(Self::MeaningCtx,Self::Meaning)> {
        match self.previous.first_meaning() {
            Some((ctx,m)) => Some((FrameMeaningCtx::Previous(ctx),
                                   FrameMeaning::Previous(m))),
            None => match self.allocations.first_meaning() {
                Some((ctx,m)) => Some((FrameMeaningCtx::Allocations(ctx),
                                       FrameMeaning::Allocations(m))),
                None => None
            }
        }
    }
    fn next_meaning(&self,ctx: &mut Self::MeaningCtx,
                    m: &mut Self::Meaning) -> bool {
        let nm = match m {
            &mut FrameMeaning::Previous(ref mut cm) => {
                let (nctx,nm) = match ctx {
                    &mut FrameMeaningCtx::Previous(ref mut cctx)
                        => if self.previous.next_meaning(cctx,cm) {
                            return true
                        } else {
                            match self.allocations.first_meaning() {
                                None => return false,
                                Some((nctx,nm))
                                    => (FrameMeaningCtx::Allocations(nctx),
                                        FrameMeaning::Allocations(nm))
                            }
                        },
                    _ => unreachable!()
                };
                *ctx = nctx;
                nm
            },
            &mut FrameMeaning::Allocations(ref mut cm) => match ctx {
                &mut FrameMeaningCtx::Allocations(ref mut cctx)
                    => return self.allocations.next_meaning(cctx,cm),
                _ => unreachable!()
            }
        };
        *m = nm;
        true
    }
}

#[derive(Clone)]
pub enum CallFrameMeaning<'b,V: Semantic+HasSorts> {
    Values(<Assoc<&'b String,V> as Semantic>::Meaning),
    Arguments(<CompVec<V> as Semantic>::Meaning),
    Activation(<Activation<'b> as Semantic>::Meaning),
    Phi(<Choice<Data<&'b String>> as Semantic>::Meaning)
}

pub enum CallFrameMeaningCtx<'b,V: Semantic+HasSorts> {
    Values(<Assoc<&'b String,V> as Semantic>::MeaningCtx),
    Arguments(<CompVec<V> as Semantic>::MeaningCtx),
    Activation(<Activation<'b> as Semantic>::MeaningCtx),
    Phi(<Choice<Data<&'b String>> as Semantic>::MeaningCtx)
}

impl<'b,V: Semantic+HasSorts> PartialEq for CallFrameMeaning<'b,V> {
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

impl<'b,V: Semantic+HasSorts> Eq for CallFrameMeaning<'b,V> {}

impl<'b,V: Semantic+HasSorts> PartialOrd for CallFrameMeaning<'b,V> {
    fn partial_cmp(&self,other: &CallFrameMeaning<'b,V>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<'b,V: Semantic+HasSorts> Ord for CallFrameMeaning<'b,V> {
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

impl<'b,V: Semantic+HasSorts> Hash for CallFrameMeaning<'b,V> {
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

impl<'b,V: Semantic+HasSorts> fmt::Debug for CallFrameMeaning<'b,V> {
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

impl<'b,V: Semantic+HasSorts> CallFrameMeaning<'b,V> {
    pub fn is_pc(&self) -> bool {
        match self {
            &CallFrameMeaning::Activation(_) => true,
            &CallFrameMeaning::Phi(_) => true,
            _ => false
        }
    }
}

impl<'b,V: Semantic+Bytes<'b>+FromConst<'b>> Semantic for CallFrame<'b,V> {
    type Meaning = CallFrameMeaning<'b,V>;
    type MeaningCtx = CallFrameMeaningCtx<'b,V>;
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
    fn first_meaning(&self) -> Option<(Self::MeaningCtx,Self::Meaning)> {
        if let Some((ctx,m)) = self.values.first_meaning() {
            Some((CallFrameMeaningCtx::Values(ctx),
                  CallFrameMeaning::Values(m)))
        } else if let Some((ctx,m)) = self.arguments.first_meaning() {
            Some((CallFrameMeaningCtx::Arguments(ctx),
                  CallFrameMeaning::Arguments(m)))
        } else if let Some((ctx,m)) = self.activation.first_meaning() {
            Some((CallFrameMeaningCtx::Activation(ctx),
                  CallFrameMeaning::Activation(m)))
        } else if let Some((ctx,m)) = self.phi.first_meaning() {
            Some((CallFrameMeaningCtx::Phi(ctx),
                  CallFrameMeaning::Phi(m)))
        } else {
            None
        }
    }
    fn next_meaning(&self,ctx: &mut Self::MeaningCtx,
                    m: &mut Self::Meaning) -> bool {
        let pos = match ctx {
            &mut CallFrameMeaningCtx::Values(ref mut cctx) => match m {
                &mut CallFrameMeaning::Values(ref mut cm) => if self.values.next_meaning(cctx,cm) {
                    return true
                } else { 0 },
                _ => unreachable!()
            },            
            &mut CallFrameMeaningCtx::Arguments(ref mut cctx) => match m {
                &mut CallFrameMeaning::Arguments(ref mut cm) => if self.arguments.next_meaning(cctx,cm) {
                    return true
                } else { 1 },
                _ => unreachable!()
            },
            &mut CallFrameMeaningCtx::Activation(ref mut cctx) => match m {
                &mut CallFrameMeaning::Activation(ref mut cm) => if self.activation.next_meaning(cctx,cm) {
                    return true
                } else { 2 },
                _ => unreachable!()
            },
            &mut CallFrameMeaningCtx::Phi(ref mut cctx) => match m {
                &mut CallFrameMeaning::Phi(ref mut cm) => if self.phi.next_meaning(cctx,cm) {
                    return true
                } else {
                    return false
                },
                _ => unreachable!()
            }
        };
        if pos==0 {
            if let Some((nctx,nm)) = self.arguments.first_meaning() {
                *ctx = CallFrameMeaningCtx::Arguments(nctx);
                *m = CallFrameMeaning::Arguments(nm);
                return true
            }
        }
        if pos<=1 {
            if let Some((nctx,nm)) = self.activation.first_meaning() {
                *ctx = CallFrameMeaningCtx::Activation(nctx);
                *m = CallFrameMeaning::Activation(nm);
                return true
            }
        }
        if let Some((nctx,nm)) = self.phi.first_meaning() {
            *ctx = CallFrameMeaningCtx::Phi(nctx);
            *m = CallFrameMeaning::Phi(nm);
            return true
        }
        false
    }
}
