extern crate smtrs;
extern crate llvm_ir;

use self::smtrs::composite::*;
use self::smtrs::embed::{Embed,DeriveConst,DeriveValues};
use self::smtrs::domain::{Domain};
use super::mem::{Bytes,FromConst,MemSlice};
use super::{InstructionRef};
use super::thread::*;
use super::frame::*;
use super::pointer::{PointerTrg};
use super::error::{Error,Errors,add_error};
use std::marker::PhantomData;
use std::fmt::Debug;
use num_bigint::BigInt;

const STEP_BW: usize = 32;

pub type ThreadId<'a> = (Option<InstructionRef<'a>>,&'a String);

pub type Threads<'a,V> = Assoc<ThreadId<'a>,
                               Vec<Thread<'a,V>>>;

pub type Globals<'a,V> = Assoc<&'a String,MemSlice<'a,V>>;

pub type Heap<'a,V> = Assoc<InstructionRef<'a>,Vec<MemSlice<'a,V>>>;

pub type Step<'a> = Choice<(Data<ThreadId<'a>>,
                            SingletonBitVec)>;

pub type Nondet<'a,V> = Assoc<InstructionRef<'a>,V>;

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub struct Program<'a,V> {
    threads: Threads<'a,V>,
    global: Globals<'a,V>,
    heap: Heap<'a,V>
}

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub struct ProgramInput<'a,V> {
    step: Step<'a>,
    nondet: Nondet<'a,V>
}

impl<'a,V : Bytes+FromConst<'a>+Clone> Program<'a,V> {
    pub fn new() -> Self {
        Program { threads: Assoc::new(),
                  global: Assoc::new(),
                  heap: Assoc::new() }
    }
}

impl<'a,V : Bytes+Clone> ProgramInput<'a,V> {
    pub fn new() -> Self {
        ProgramInput { step: Choice::new(),
                       nondet: Assoc::new() }
    }
    pub fn add_thread(&mut self,thread_id: ThreadId<'a>) -> () {
        self.step.add((Data(thread_id),SingletonBitVec(STEP_BW)));
    }
}

pub fn program_input_thread_activation<'a,'b,V,Em>(inp: &ProgramInput<'b,V>,
                                                   inp_inp: Transf<Em>,
                                                   thread_id: &ThreadId<'b>,
                                                   em: &mut Em)
                                                   -> Result<Option<(Transf<Em>,Transf<Em>)>,Em::Error>
    where V : Bytes + Clone, Em : Embed {
    match inp.step.choices(inp_inp).find(|&(&(ref dat,_),_,_)| dat.0==*thread_id) {
        None => Ok(None),
        Some((_,cond,idx)) => Ok(Some((cond,idx)))
    }
}

pub fn program_get_thread<'a,'b,V,Em>(prog: OptRef<'a,Program<'b,V>>,
                                      prog_inp: Transf<Em>,
                                      thread_id: &ThreadId<'b>,
                                      idx: Transf<Em>,
                                      exprs: &[Em::Expr],
                                      em: &mut Em)
                                      -> Result<Option<(OptRef<'a,Thread<'b,V>>,Transf<Em>)>,Em::Error>
    where V : Bytes+FromConst<'b>+Clone, Em : DeriveConst {

    let (threads,threads_inp) = program_get_threads(prog,prog_inp);
    match assoc_get(threads,threads_inp,thread_id)? {
        None => Ok(None),
        Some((st,st_inp)) => get_vec_elem_dyn(st,idx,st_inp,exprs,em)
    }
}

pub fn program_get_ptr_trg<'a,'b,V,Em>(trg: OptRef<'a,PointerTrg<'b>>,
                                       prog: OptRef<'a,Program<'b,V>>,
                                       errs: OptRef<'a,Errors<'b>>,
                                       inp_trg: Transf<Em>,
                                       inp_prog: Transf<Em>,
                                       inp_errs: Transf<Em>,
                                       exprs: &[Em::Expr],
                                       em: &mut Em)
                                       -> Result<(Option<(OptRef<'a,MemSlice<'b,V>>,Transf<Em>)>,OptRef<'a,Errors<'b>>,Transf<Em>),Em::Error>
    where V : Bytes+FromConst<'b>+Clone, Em : DeriveConst {
    match trg.as_ref() {
        &PointerTrg::Null => {
            let (nerrs,ninp_errs) = add_error(errs,inp_errs,&Error::NullPointerDeref,em)?;
            Ok((None,nerrs,ninp_errs))
        },
        &PointerTrg::Global(ref name) => {
            let (glb,glb_inp) = program_get_global(prog,inp_prog);
            match assoc_get(glb,glb_inp,name)? {
                None => {
                    let (nerrs,ninp_errs) = add_error(errs,inp_errs,&Error::UnknownGlobal(name),em)?;
                    Ok((None,nerrs,ninp_errs))
                },
                Some((sl,inp_sl)) => Ok((Some((sl,inp_sl)),errs,inp_errs))
            }
        },
        &PointerTrg::Heap(ref malloc,_) => {
            let (hp,inp_hp) = program_get_heap(prog,inp_prog);
            match assoc_get(hp,inp_hp,malloc)? {
                None => {
                    let (nerrs,ninp_errs) = add_error(errs,inp_errs,&Error::UnknownHeapLocation(malloc.clone()),em)?;
                    Ok((None,nerrs,ninp_errs))
                },
                Some((st,inp_st)) => match get_vec_elem_dyn(st,inp_trg,inp_st,exprs,em)? {
                    None => {
                        let (nerrs,ninp_errs) = add_error(errs,inp_errs,&Error::UnknownHeapIndex(malloc.clone()),em)?;
                        Ok((None,nerrs,ninp_errs))
                    },
                    Some((sl,inp_sl)) => Ok((Some((sl,inp_sl)),errs,inp_errs))
                }
            }
        },
        &PointerTrg::Stack(ref thr_id,_,
                           ref fr_id,_,
                           ref alloc_instr,_) => {
            let (thrs,inp_thrs) = program_get_threads(prog,inp_prog);
            match assoc_get(thrs,inp_thrs,thr_id)? {
                None => {
                    let (nerrs,ninp_errs) = add_error(errs,inp_errs,&Error::UnknownThread(thr_id.clone()),em)?;
                    Ok((None,nerrs,ninp_errs))
                },
                Some((st,inp_st)) => match get_vec_elem_dyn(st,Transformation::view(0,1,inp_trg.clone()),inp_st,exprs,em)? {
                    None => {
                        let (nerrs,ninp_errs) = add_error(errs,inp_errs,&Error::UnknownThreadIndex(thr_id.clone()),em)?;
                        Ok((None,nerrs,ninp_errs))
                    },
                    Some((thr,inp_thr)) => match thread_get_frame(thr,inp_thr,fr_id,Transformation::view(1,1,inp_trg.clone()),exprs,em)? {
                        None => {
                            let (nerrs,ninp_errs) = add_error(errs,inp_errs,&Error::UnknownFrameId(fr_id.clone()),em)?;
                            Ok((None,nerrs,ninp_errs))
                        },
                        Some((fr,fr_inp)) => {
                            let (alloc,alloc_inp) = frame_get_allocations(fr,fr_inp);
                            match assoc_get(alloc,alloc_inp,alloc_instr)? {
                                None => {
                                    let (nerrs,ninp_errs) = add_error(errs,inp_errs,&Error::UnknownAllocaInstr(alloc_instr.clone()),em)?;
                                    Ok((None,nerrs,ninp_errs))
                                },
                                Some((pool,pool_inp)) => match get_vec_elem_dyn(pool,Transformation::view(2,1,inp_trg),pool_inp,exprs,em)? {
                                    None => {
                                        let (nerrs,ninp_errs) = add_error(errs,inp_errs,&Error::UnknownAllocaIndex(alloc_instr.clone()),em)?;
                                        Ok((None,nerrs,ninp_errs))
                                    },
                                    Some((sl,sl_inp)) => Ok((Some((sl,sl_inp)),errs,inp_errs))
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

fn program_get_threads<'a,'b,V,Em>(prog: OptRef<'a,Program<'b,V>>,
                                   inp_prog: Transf<Em>)
                                   -> (OptRef<'a,Assoc<ThreadId<'b>,Vec<Thread<'b,V>>>>,Transf<Em>)
    where V : Bytes+FromConst<'b>+Clone,Em : Embed {
    let sz = prog.as_ref().threads.num_elem();
    let thr = match prog {
        OptRef::Ref(ref rprog) => OptRef::Ref(&rprog.threads),
        OptRef::Owned(rprog) => OptRef::Owned(rprog.threads)
    };
    let thr_inp = Transformation::view(0,sz,inp_prog);
    (thr,thr_inp)
}

fn program_get_global<'a,'b,V,Em>(prog: OptRef<'a,Program<'b,V>>,
                                  inp_prog: Transf<Em>)
                                  -> (OptRef<'a,Assoc<&'b String,MemSlice<'b,V>>>,Transf<Em>)
    where V : Bytes+FromConst<'b>+Clone,Em : Embed {
    let off = prog.as_ref().threads.num_elem();
    let sz = prog.as_ref().global.num_elem();
    let glb = match prog {
        OptRef::Ref(ref rprog) => OptRef::Ref(&rprog.global),
        OptRef::Owned(rprog) => OptRef::Owned(rprog.global)
    };
    let glb_inp = Transformation::view(off,sz,inp_prog);
    (glb,glb_inp)
}

fn program_get_heap<'a,'b,V,Em>(prog: OptRef<'a,Program<'b,V>>,
                                inp_prog: Transf<Em>)
                                -> (OptRef<'a,Assoc<InstructionRef<'b>,Vec<MemSlice<'b,V>>>>,Transf<Em>)
    where V : Bytes+FromConst<'b>+Clone,Em : Embed {
    let off = prog.as_ref().threads.num_elem() +
        prog.as_ref().global.num_elem();
    let sz = prog.as_ref().heap.num_elem();
    let hp = match prog {
        OptRef::Ref(ref rprog) => OptRef::Ref(&rprog.heap),
        OptRef::Owned(rprog) => OptRef::Owned(rprog.heap)
    };
    let hp_inp = Transformation::view(off,sz,inp_prog);
    (hp,hp_inp)
}

pub fn program<'a,'b,'c,V,Em>(thrs: OptRef<'a,Threads<'b,V>>,
                              inp_thrs: Transf<Em>,
                              glob: OptRef<'a,Globals<'b,V>>,
                              inp_glob: Transf<Em>,
                              heap: OptRef<'a,Heap<'b,V>>,
                              inp_heap: Transf<Em>)
                              -> (OptRef<'c,Program<'b,V>>,Transf<Em>)
    where V : Bytes+FromConst<'b>+Clone,Em : Embed {
    debug_assert_eq!(thrs.as_ref().num_elem(),inp_thrs.size());
    debug_assert_eq!(glob.as_ref().num_elem(),inp_glob.size());
    debug_assert_eq!(heap.as_ref().num_elem(),inp_heap.size());

    let prog = Program { threads: thrs.as_obj(),
                         global: glob.as_obj(),
                         heap: heap.as_obj() };
    let prog_inp = Transformation::concat(&[inp_thrs,inp_glob,inp_heap]);
    (OptRef::Owned(prog),prog_inp)
}

pub fn program_input<'a,'b,'c,V,Em>(step: OptRef<'a,Step<'b>>,
                                    inp_step: Transf<Em>,
                                    nondet: OptRef<'a,Nondet<'b,V>>,
                                    inp_nondet: Transf<Em>)
                                    -> (OptRef<'c,ProgramInput<'b,V>>,Transf<Em>)
    where V : Bytes + Clone,Em : Embed {
    debug_assert_eq!(step.as_ref().num_elem(),inp_step.size());
    debug_assert_eq!(nondet.as_ref().num_elem(),inp_nondet.size());

    let pinp = ProgramInput { step: step.as_obj(),
                              nondet: nondet.as_obj() };
    let inp_pinp = Transformation::concat(&[inp_step,inp_nondet]);
    (OptRef::Owned(pinp),inp_pinp)
}

pub fn decompose_program<'a,'b,V,Em>(prog: OptRef<'a,Program<'b,V>>,
                                     inp_prog: Transf<Em>)
                                     -> (OptRef<'a,Threads<'b,V>>,
                                         Transf<Em>,
                                         OptRef<'a,Globals<'b,V>>,
                                         Transf<Em>,
                                         OptRef<'a,Heap<'b,V>>,
                                         Transf<Em>)
    where V : Bytes+FromConst<'b>+Clone,Em : Embed {
    let (thrs,glob,hp) = match prog {
        OptRef::Ref(ref prog)
            => (OptRef::Ref(&prog.threads),
                OptRef::Ref(&prog.global),
                OptRef::Ref(&prog.heap)),
        OptRef::Owned(prog)
            => (OptRef::Owned(prog.threads),
                OptRef::Owned(prog.global),
                OptRef::Owned(prog.heap))
    };
    let sz_thrs = thrs.as_ref().num_elem();
    let sz_glob = glob.as_ref().num_elem();
    let sz_hp = hp.as_ref().num_elem();
    let inp_thrs = Transformation::view(0,sz_thrs,inp_prog.clone());
    let inp_glob = Transformation::view(sz_thrs,sz_glob,inp_prog.clone());
    let inp_hp = Transformation::view(sz_thrs+sz_glob,sz_hp,inp_prog);
    (thrs,inp_thrs,glob,inp_glob,hp,inp_hp)
}

fn decompose_program_input<'a,'b,V>(x: OptRef<'a,ProgramInput<'b,V>>)
                                    -> (OptRef<'a,Choice<(Data<ThreadId<'b>>,
                                                          SingletonBitVec)>>,
                                        OptRef<'a,Assoc<InstructionRef<'b>,V>>)
    where V : Bytes + Clone {
    match x {
        OptRef::Ref(ref rx) => (OptRef::Ref(&rx.step),
                                OptRef::Ref(&rx.nondet)),
        OptRef::Owned(rx) => (OptRef::Owned(rx.step),
                              OptRef::Owned(rx.nondet))
    }
}
impl<'b,V : Bytes+FromConst<'b>+Clone> Composite for Program<'b,V> {
    fn num_elem(&self) -> usize {
        self.threads.num_elem() +
            self.global.num_elem() +
            self.heap.num_elem()
    }
    fn elem_sort<Em : Embed>(&self,pos: usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        let off1 = self.threads.num_elem();
        if pos < off1 {
            return self.threads.elem_sort(pos,em)
        }
        let off2 = off1+self.global.num_elem();
        if pos < off2 {
            return self.global.elem_sort(pos-off1,em)
        }
        debug_assert!({ let off3 = off2+self.heap.num_elem();
                        pos < off3 });
        self.heap.elem_sort(pos-off2,em)
    }
    fn combine<'a,Em,FComb,FL,FR>(x: OptRef<'a,Self>,y: OptRef<'a,Self>,
                                  inp_x: Transf<Em>,inp_y: Transf<Em>,
                                  comb: &FComb,only_l: &FL,only_r: &FR,em: &mut Em)
                                  -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>
        where Em : Embed,
              FComb : Fn(Transf<Em>,Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FL : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FR : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error> {
        let (thr_x,inp_thr_x,glb_x,inp_glb_x,hp_x,inp_hp_x) = decompose_program(x,inp_x);
        let (thr_y,inp_thr_y,glb_y,inp_glb_y,hp_y,inp_hp_y) = decompose_program(y,inp_y);

        let (thr,inp_thr) = match Assoc::combine(thr_x,thr_y,
                                                 inp_thr_x,inp_thr_y,
                                                 comb,only_l,only_r,em)? {
            None => return Ok(None),
            Some(r) => r
        };

        let (glb,inp_glb) = match Assoc::combine(glb_x,glb_y,
                                                 inp_glb_x,inp_glb_y,
                                                 comb,only_l,only_r,em)? {
            None => return Ok(None),
            Some(r) => r
        };

        let (hp,inp_hp) = match Assoc::combine(hp_x,hp_y,
                                               inp_hp_x,inp_hp_y,
                                               comb,only_l,only_r,em)? {
            None => return Ok(None),
            Some(r) => r
        };

        Ok(Some((OptRef::Owned(Program { threads: thr.as_obj(),
                                         global: glb.as_obj(),
                                         heap: hp.as_obj() }),
                 Transformation::concat(&[inp_thr,inp_glb,inp_hp]))))
    }
}

impl<'b,V : Bytes + Clone> Composite for ProgramInput<'b,V> {
    fn num_elem(&self) -> usize {
        self.step.num_elem() +
            self.nondet.num_elem()
    }
    fn elem_sort<Em : Embed>(&self,pos: usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        let off1 = self.step.num_elem();
        if pos < off1 {
            return self.step.elem_sort(pos,em);
        }
        debug_assert!({ let off2 = off1+self.nondet.num_elem();
                        pos < off2 });
        self.nondet.elem_sort(pos-off1,em)
    }
    fn combine<'a,Em,FComb,FL,FR>(x: OptRef<'a,Self>,y: OptRef<'a,Self>,
                                  inp_x: Transf<Em>,inp_y: Transf<Em>,
                                  comb: &FComb,only_l: &FL,only_r: &FR,em: &mut Em)
                                  -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>
        where Em : Embed,
              FComb : Fn(Transf<Em>,Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FL : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FR : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error> {

        let (step_x,nondet_x) = decompose_program_input(x);
        let (step_y,nondet_y) = decompose_program_input(y);

        let sz1_x = step_x.as_ref().num_elem();
        let sz1_y = step_y.as_ref().num_elem();
        
        let (step,step_inp) = match Choice::combine(step_x,step_y,
                                                    Transformation::view(0,sz1_x,inp_x.clone()),
                                                    Transformation::view(0,sz1_y,inp_y.clone()),
                                                    comb,only_l,only_r,em)? {
            None => return Ok(None),
            Some(r) => r
        };

        let sz2_x = nondet_x.as_ref().num_elem();
        let sz2_y = nondet_y.as_ref().num_elem();

        let (nondet,nondet_inp) = match Assoc::combine(nondet_x,nondet_y,
                                                       Transformation::view(sz1_x,sz2_x,inp_x),
                                                       Transformation::view(sz1_y,sz2_y,inp_y),
                                                       comb,only_l,only_r,em)? {
            None => return Ok(None),
            Some(r) => r
        };

        Ok(Some((OptRef::Owned(ProgramInput { step: step.as_obj(),
                                              nondet: nondet.as_obj() }),
                 Transformation::concat(&[step_inp,nondet_inp]))))
    }
}

// Views for Program

#[derive(Clone,PartialEq,Eq)]
pub struct ThreadsView<'a,V : 'a>(PhantomData<&'a V>);

#[derive(Clone,PartialEq,Eq)]
pub struct GlobalsView<'a,V : 'a>(PhantomData<&'a V>);

#[derive(Clone,PartialEq,Eq)]
pub struct HeapView<'a,V : 'a>(PhantomData<&'a V>);

impl<'a,V : 'a+Bytes+FromConst<'a>> View for ThreadsView<'a,V> {
    type Viewed = Program<'a,V>;
    type Element = Threads<'a,V>;
    fn get_el<'b>(&self,prog: &'b Self::Viewed)
                  -> &'b Self::Element where Self : 'b {
        &prog.threads
    }
    fn get_el_ext<'b>(&self,prog: &'b Self::Viewed)
                      -> (usize,&'b Self::Element) where Self : 'b {
        (0,&prog.threads)
    }
}

impl<'a,V : 'a+Bytes+FromConst<'a>> View for GlobalsView<'a,V> {
    type Viewed = Program<'a,V>;
    type Element = Globals<'a,V>;
    fn get_el<'b>(&self,prog: &'b Self::Viewed)
                  -> &'b Self::Element where Self : 'b {
        &prog.global
    }
    fn get_el_ext<'b>(&self,prog: &'b Self::Viewed)
                      -> (usize,&'b Self::Element) where Self : 'b {
        (prog.threads.num_elem(),&prog.global)
    }
}

impl<'a,V : 'a+Bytes+FromConst<'a>> View for HeapView<'a,V> {
    type Viewed = Program<'a,V>;
    type Element = Heap<'a,V>;
    fn get_el<'b>(&self,prog: &'b Self::Viewed)
                  -> &'b Self::Element where Self : 'b {
        &prog.heap
    }
    fn get_el_ext<'b>(&self,prog: &'b Self::Viewed)
                      -> (usize,&'b Self::Element) where Self : 'b {
        (prog.threads.num_elem()+
         prog.global.num_elem(),&prog.heap)
    }
}

impl<'a,V : 'a+Bytes+FromConst<'a>> ViewMut for ThreadsView<'a,V> {
    fn get_el_mut<'b>(&self,prog: &'b mut Self::Viewed)
                      -> &'b mut Self::Element where Self : 'b {
        &mut prog.threads
    }
    fn get_el_mut_ext<'b>(&self,prog: &'b mut Self::Viewed)
                          -> (usize,&'b mut Self::Element) where Self : 'b {
        (0,&mut prog.threads)
    }
}

impl<'a,V : 'a+Bytes+FromConst<'a>> ViewMut for GlobalsView<'a,V> {
    fn get_el_mut<'b>(&self,prog: &'b mut Self::Viewed)
                      -> &'b mut Self::Element where Self : 'b {
        &mut prog.global
    }
    fn get_el_mut_ext<'b>(&self,prog: &'b mut Self::Viewed)
                          -> (usize,&'b mut Self::Element) where Self : 'b {
        (prog.threads.num_elem(),&mut prog.global)
    }
}

impl<'a,V : 'a+Bytes+FromConst<'a>> ViewMut for HeapView<'a,V> {
    fn get_el_mut<'b>(&self,prog: &'b mut Self::Viewed)
                      -> &'b mut Self::Element where Self : 'b {
        &mut prog.heap
    }
    fn get_el_mut_ext<'b>(&self,prog: &'b mut Self::Viewed)
                          -> (usize,&'b mut Self::Element) where Self : 'b {
        (prog.threads.num_elem()+
         prog.global.num_elem(),&mut prog.heap)
    }
}

impl<'a,V> ThreadsView<'a,V> {
    pub fn new() -> Self {
        ThreadsView(PhantomData)
    }
}

impl<'a,V> GlobalsView<'a,V> {
    pub fn new() -> Self {
        GlobalsView(PhantomData)
    }
}

impl<'a,V> HeapView<'a,V> {
    pub fn new() -> Self {
        HeapView(PhantomData)
    }
}

pub struct CurrentThreadIter<'a,V,Em : DeriveValues> {
    phantom: PhantomData<V>,
    step: Transf<Em>,
    thr_id: ThreadId<'a>,
    iter: IndexedIter<Em>
}

impl<'a,Em : DeriveValues,V : 'a+Bytes+FromConst<'a>+Clone
     > CurrentThreadIter<'a,V,Em> {
    pub fn new(prog: &'a Program<'a,V>,
               thr_id: ThreadId<'a>,
               step: Transf<Em>,
               thr_idx: Transf<Em>,
               exprs: &[Em::Expr],
               em: &mut Em) -> Result<CurrentThreadIter<'a,V,Em>,Em::Error> {
        Ok(CurrentThreadIter {
            phantom: PhantomData,
            step: step,
            thr_id: thr_id,
            iter: access_dyn(prog.threads.access(&thr_id),thr_idx,exprs,em)?
        })
    }
}

impl<'a,V,Em : DeriveValues> Clone for CurrentThreadIter<'a,V,Em> {
    fn clone(&self) -> Self {
        CurrentThreadIter {
            phantom: PhantomData,
            step: self.step.clone(),
            thr_id: self.thr_id.clone(),
            iter: self.iter.clone()
        }
    }
}

pub type ThreadView<'a,V> = Then<ThreadsView<'a,V>,
                                 Then<AssocView<ThreadId<'a>,Vec<Thread<'a,V>>>,
                                      VecView<Thread<'a,V>>>>;

pub fn thread_view_to_idx<'a,V,Em : Embed>(view: &ThreadView<'a,V>,bw: usize,em: &mut Em)
                                           -> Result<(ThreadId<'a>,Transf<Em>),Em::Error> {
    let &Then(_,Then(ref assoc,ref vec)) = view;
    let e = em.const_bitvec(bw,BigInt::from(vec.idx))?;
    let inp = Transformation::constant(vec![e]);
    Ok((assoc.key.clone(),inp))
}

impl<'a,Em : DeriveValues,V : 'a> CondIterator<Em> for CurrentThreadIter<'a,V,Em> {
    type Item = ThreadView<'a,V>;
    fn next(&mut self,conds: &mut Vec<Transf<Em>>,pos: usize,em: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        if conds.len()==pos {
            conds.push(self.step.clone());
        }
        match self.iter.next(conds,pos+1,em)? {
            None => Ok(None),
            Some(i) => Ok(Some(Then::new(ThreadsView::new(),
                                         Then::new(AssocView::new(self.thr_id.clone()),
                                                   VecView::new(i)))))
        }
    }
}

type TopFrameIdIter<'a,It,V,Em>
    = SeqPure<It,Context<GetterElement<'a,Choice<Data<Option<ContextId<'a>>>>,
                                       Chosen<'a,Data<Option<ContextId<'a>>>,Em>>,ThreadView<'a,V>>,
              (&'a Program<'a,V>,
               Transf<Em>),
              fn(&(&'a Program<'a,V>,
                   Transf<Em>),
                 ThreadView<'a,V>) -> Context<GetterElement<'a,Choice<Data<Option<ContextId<'a>>>>,
                                                            Chosen<'a,Data<Option<ContextId<'a>>>,Em>>,ThreadView<'a,V>>>;

pub fn get_frame_id_iter<'a,V,Em>(ctx: &(&'a Program<'a,V>,
                                         Transf<Em>),
                                  thr_view: ThreadView<'a,V>)
                                  -> Context<GetterElement<'a,Choice<Data<Option<ContextId<'a>>>>,
                                                           Chosen<'a,Data<Option<ContextId<'a>>>,Em>>,ThreadView<'a,V>>
    where Em : Embed, V : Bytes+FromConst<'a> {
    
    let (top_off,top) = thr_view.clone().then(StackTopView::new()).get_el_ext(ctx.0);
    let top_inp = Transformation::view(top_off,top.num_elem(),ctx.1.clone());
    top.chosen(top_inp).get_element(top).context(thr_view)
}


pub fn top_frame_id_iter<'a,V,It,Em>(prog: &'a Program<'a,V>,
                                     prog_inp: Transf<Em>,
                                     prev: It) -> TopFrameIdIter<'a,It,V,Em>
    where Em : Embed, It : CondIterator<Em,Item=ThreadView<'a,V>>, V : Bytes+FromConst<'a> {
    prev.seq_pure((prog,prog_inp),get_frame_id_iter)
}

//type FrameIdToFrameView<'a,V,It,Em>
//    = 

pub enum FrameIter<'a,V : 'a,Em : DeriveValues> {
    Call(BeforeIterator<CallStackView<'a,V>,
                        BeforeIterator<AssocView<CallId<'a>,
                                                 BitVecVectorStack<(CallFrame<'a,V>,Frame<'a,V>)>>,
                                       ThenIterator<SndView<CallFrame<'a,V>,Frame<'a,V>>,
                                                    BitVecVectorStackAccess<(CallFrame<'a,V>,Frame<'a,V>),Em>>>>),
    Stack(BeforeIterator<StackView<'a,V>,
                         BeforeIterator<AssocView<InstructionRef<'a>,
                                                  BitVecVectorStack<Frame<'a,V>>>,
                                        BitVecVectorStackAccess<Frame<'a,V>,Em>>>)
}

impl<'a,V : 'a,Em : DeriveValues> Clone for FrameIter<'a,V,Em> {
    fn clone(&self) -> Self {
        match self {
            &FrameIter::Call(ref it) => FrameIter::Call(it.clone()),
            &FrameIter::Stack(ref it) => FrameIter::Stack(it.clone())
        }
    }
}

impl<'a,V,Em : DeriveValues> CondIterator<Em> for FrameIter<'a,V,Em>
    where V : Bytes+FromConst<'a> {
    
    type Item = FrameView<'a,V>;
    fn next(&mut self,conds: &mut Vec<Transf<Em>>,pos: usize,em: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        match self {
            &mut FrameIter::Call(ref mut it) => match it.next(conds,pos,em)? {
                None => Ok(None),
                Some(v) => Ok(Some(FrameView::Call(v)))
            },
            &mut FrameIter::Stack(ref mut it) => match it.next(conds,pos,em)? {
                None => Ok(None),
                Some(v) => Ok(Some(FrameView::Stack(v)))
            }
        }
    }    
}

pub fn frame_id_to_frame_iter<'a,V,Em>
    (ctx: &(&Program<'a,V>,Transf<Em>,&[Em::Expr]),
     el: (ThreadView<'a,V>,ContextId<'a>),
     em: &mut Em)
     -> Result<BeforeIterator<ThreadView<'a,V>,
                              FrameIter<'a,V,Em>>,Em::Error>
    where Em : DeriveValues, V : 'a+Bytes+FromConst<'a> {
    let thr_view = el.0;
    let fr_id = el.1;
    match fr_id {
        ContextId::Call(cid) => {
            let cs_view = thr_view.clone()
                .then(Then::new(CallStackView::new(),
                                AssocView::new(cid.clone())));
            let (cs_off,cs) = cs_view.get_el_ext(&ctx.0);
            let cs_inp = Transformation::view(cs_off,cs.num_elem(),ctx.1.clone());
            Ok(FrameIter::Call(cs.access_top(cs_inp,ctx.2,em)?
                               .then(SndView::new())
                               .before(AssocView::new(cid.clone()))
                               .before(CallStackView::new()))
               .before(thr_view))
        },
        ContextId::Stack(cid,instr) => {
            let st_view = thr_view.clone()
                .then(Then::new(StackView::new(),
                                AssocView::new(instr.clone())));
            let (st_off,st) = st_view.get_el_ext(&ctx.0);
            let st_inp = Transformation::view(st_off,st.num_elem(),ctx.1.clone());
            Ok(FrameIter::Stack(st.access_top(st_inp,ctx.2,em)?
                                .before(AssocView::new(instr.clone()))
                                .before(StackView::new()))
               .before(thr_view))
        }
    }
}

type CallFrameIter<'a,V,Em>
    = BeforeIterator<ThreadView<'a,V>,
                     BeforeIterator<CallStackView<'a,V>,
                                    BeforeIterator<AssocView<CallId<'a>,
                                                             BitVecVectorStack<(CallFrame<'a,V>,Frame<'a,V>)>>,
                                                   ThenIterator<FstView<CallFrame<'a,V>,Frame<'a,V>>,
                                                                BitVecVectorStackAccess<(CallFrame<'a,V>,Frame<'a,V>),Em>>>>>;

pub fn frame_id_to_call_frame_iter<'a,V,Em>(ctx: &(&Program<'a,V>,Transf<Em>,&[Em::Expr]),
                                            el: (ThreadView<'a,V>,ContextId<'a>),
                                            em: &mut Em)
                                            -> Result<CallFrameIter<'a,V,Em>,Em::Error>
    where Em : DeriveValues, V : 'a+Bytes+FromConst<'a> {
    let thr_view = el.0;
    let fr_id = el.1;
    match fr_id {
        ContextId::Call(cid) |
        ContextId::Stack(cid,_) => {
            let cs_view = thr_view.clone()
                .then(Then::new(CallStackView::new(),
                                AssocView::new(cid.clone())));
            let (cs_off,cs) = cs_view.get_el_ext(&ctx.0);
            let cs_inp = Transformation::view(cs_off,cs.num_elem(),ctx.1.clone());
            Ok(cs.access_top(cs_inp,ctx.2,em)?
               .then(FstView::new())
               .before(AssocView::new(cid.clone()))
               .before(CallStackView::new())
               .before(thr_view))
        }
    }
}

pub struct CurrentCallFrameIter<'a,It,V : 'a,Em : DeriveValues>
    where Em::Expr : 'a {
    prog: &'a Program<'a,V>,
    inp_prog: Transf<Em>,
    thread_iter: It,
    cf_id: CallId<'a>,
    exprs: &'a [Em::Expr],
    cur_iter: Option<(Then<ThreadView<'a,V>,
                           Then<CallStackView<'a,V>,
                                AssocView<CallId<'a>,
                                          BitVecVectorStack<(CallFrame<'a,V>,Frame<'a,V>)>>>>,
                      usize,&'a BitVecVectorStack<(CallFrame<'a,V>,Frame<'a,V>)>,
                      BitVecVectorStackAccess<(CallFrame<'a,V>,Frame<'a,V>),Em>,usize)>
}

impl<'a,It,V,Em : DeriveValues> CurrentCallFrameIter<'a,It,V,Em>
    where It : CondIterator<Em,Item=ThreadView<'a,V>>,
          V : 'a+Bytes+FromConst<'a> {
    pub fn new(prog: &'a Program<'a,V>,
               inp_prog: Transf<Em>,
               iter: It,
               cf_id: CallId<'a>,
               exprs: &'a [Em::Expr]) -> Self {
        CurrentCallFrameIter { prog: prog,
                               inp_prog: inp_prog,
                               thread_iter: iter,
                               cf_id: cf_id,
                               exprs: exprs,
                               cur_iter: None }
    }
    fn take_cur_iter(&mut self,
                     conds: &mut Vec<Transf<Em>>,
                     pos: usize,
                     em: &mut Em)
                     -> Result<Option<(Then<ThreadView<'a,V>,
                                            Then<CallStackView<'a,V>,
                                                 AssocView<CallId<'a>,
                                                           BitVecVectorStack<(CallFrame<'a,V>,Frame<'a,V>)>>>>,
                                       usize,&'a BitVecVectorStack<(CallFrame<'a,V>,Frame<'a,V>)>,
                                       BitVecVectorStackAccess<(CallFrame<'a,V>,
                                                                Frame<'a,V>),Em>,usize)>,Em::Error> {
        match self.cur_iter.take() {
            Some(res) => Ok(Some(res)),
            None => {
                conds.truncate(pos);
                match self.thread_iter.next(conds,pos,em)? {
                    None => Ok(None),
                    Some(thr_view) => {
                        let css_view = CallStackView::new();
                        let cs_view = Then::new(thr_view,
                                                Then::new(css_view,
                                                          AssocView::new(self.cf_id)));
                        let npos = conds.len();
                        let (cs_off,cs) = cs_view.get_el_ext(self.prog);
                        let cs_inp = Transformation::view(cs_off,
                                                          cs.num_elem(),
                                                          self.inp_prog.clone());
                        let it = cs.access_top(cs_inp,self.exprs,em)?;
                        Ok(Some((cs_view,cs_off,cs,it,npos)))
                    }
                }
            }
        }
    }
}

impl<'a,It,V,Em : DeriveValues> CondIterator<Em> for CurrentCallFrameIter<'a,It,V,Em>
    where It : CondIterator<Em,Item=ThreadView<'a,V>>,
          V : 'a+Bytes+FromConst<'a> {
    type Item = Then<Then<ThreadView<'a,V>,
                          Then<CallStackView<'a,V>,
                               AssocView<CallId<'a>,
                                         BitVecVectorStack<(CallFrame<'a,V>,Frame<'a,V>)>>>>,
                     BitVecVectorStackView<(CallFrame<'a,V>,Frame<'a,V>)>>;
    fn next(&mut self,conds: &mut Vec<Transf<Em>>,pos: usize,em: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        while let Some((cs_view,cs_off,cs,mut it,npos)) = self.take_cur_iter(conds,pos,em)? {
            match it.next(conds,npos,em)? {
                None => continue,
                Some(el) => {
                    self.cur_iter = Some((cs_view.clone(),cs_off,cs,it,npos));
                    let r_view = Then::new(cs_view,el);
                    return Ok(Some(r_view))
                }
            }
        }
        Ok(None)
    }
}

pub enum PointerView<'a,V : 'a> {
    Global(Then<GlobalsView<'a,V>,
                AssocView<&'a String,MemSlice<'a,V>>>),
    Heap(Then<HeapView<'a,V>,
              Then<AssocView<InstructionRef<'a>,
                             Vec<MemSlice<'a,V>>>,
                   VecView<MemSlice<'a,V>>>>),
    Stack(Then<ThreadsView<'a,V>,
               Then<AssocView<ThreadId<'a>,
                              Vec<Thread<'a,V>>>,
                    Then<VecView<Thread<'a,V>>,
                         Then<FrameView<'a,V>,
                              Then<AllocationsView<'a,V>,
                                   Then<AssocView<InstructionRef<'a>,
                                                  Vec<MemSlice<'a,V>>>,
                                        VecView<MemSlice<'a,V>>>>>>>>)
}

impl<'a,V> View for PointerView<'a,V>
    where V : 'a+Bytes+FromConst<'a> {
    type Viewed = Program<'a,V>;
    type Element = MemSlice<'a,V>;
    fn get_el<'b>(&self,obj: &'b Self::Viewed)
                  -> &'b Self::Element where Self : 'b {
        match self {
            &PointerView::Global(ref view)
                => view.get_el(obj),
            &PointerView::Heap(ref view)
                => view.get_el(obj),
            &PointerView::Stack(ref view)
                => view.get_el(obj)
        }
    }
    fn get_el_ext<'b>(&self,obj: &'b Self::Viewed)
                      -> (usize,&'b Self::Element) where Self : 'b {
        match self {
            &PointerView::Global(ref view)
                => view.get_el_ext(obj),
            &PointerView::Heap(ref view)
                => view.get_el_ext(obj),
            &PointerView::Stack(ref view)
                => view.get_el_ext(obj)
        }
    }
}
