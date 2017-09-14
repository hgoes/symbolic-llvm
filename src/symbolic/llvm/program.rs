extern crate smtrs;

use self::smtrs::composite::*;
use self::smtrs::embed::{Embed,DeriveConst,DeriveValues};
use self::smtrs::domain::{Domain};
use super::mem::{Bytes,MemSlice};
use super::{InstructionRef};
use super::thread::{Thread,thread_get_frame};
use super::frame::frame_get_allocations;
use super::pointer::{PointerTrg};
use super::error::{Error,Errors,add_error};
use std::fmt::Debug;

const STEP_BW: usize = 32;

pub type ThreadId<'a> = (Option<InstructionRef<'a>>,&'a String);

pub type Threads<'a,V> = Assoc<ThreadId<'a>,
                               Vec<Thread<'a,V>>>;

pub type Globals<'a,V> = Assoc<&'a String,MemSlice<V>>;

pub type Heap<'a,V> = Assoc<InstructionRef<'a>,Vec<MemSlice<V>>>;

pub type Step<'a> = Choice<(Data<ThreadId<'a>>,
                            SingletonBitVec)>;

pub type Nondet<'a,V> = Assoc<InstructionRef<'a>,V>;

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub struct Program<'a,V : Bytes + Clone> {
    threads: Threads<'a,V>,
    global: Globals<'a,V>,
    heap: Heap<'a,V>
}

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub struct ProgramInput<'a,V : Bytes + Clone> {
    step: Step<'a>,
    nondet: Nondet<'a,V>
}

impl<'a,V : Bytes+Clone> Program<'a,V> {
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

pub fn program_input_thread_activation<'a,'b,V,Em>(inp: OptRef<'a,ProgramInput<'b,V>>,
                                                   inp_inp: Transf<Em>,
                                                   thread_id: &ThreadId<'b>,
                                                   em: &mut Em)
                                                   -> Result<Option<(Transf<Em>,Transf<Em>)>,Em::Error>
    where V : Bytes + Clone, Em : Embed {
    match inp.as_ref().step.choices(inp_inp).find(|&(&(ref dat,_),_,_)| dat.0==*thread_id) {
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
    where V : Bytes + Clone, Em : DeriveConst {

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
                                       -> Result<(Option<(OptRef<'a,MemSlice<V>>,Transf<Em>)>,OptRef<'a,Errors<'b>>,Transf<Em>),Em::Error>
    where V : Bytes + Clone, Em : DeriveConst {
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
                                   -> (OptRef<'a,Assoc<(Option<InstructionRef<'b>>,&'b String),Vec<Thread<'b,V>>>>,Transf<Em>)
    where V : Bytes+Clone,Em : Embed {
    let sz = prog.as_ref().threads.num_elem();
    let thr = match prog {
        OptRef::Ref(ref rprog) => OptRef::Ref(&rprog.threads),
        OptRef::Owned(rprog) => OptRef::Owned(rprog.threads)
    };
    let thr_inp = Transformation::view(0,sz,inp_prog);
    (thr,thr_inp)
}

fn program_get_global<'a,V,Em>(prog: OptRef<'a,Program<'a,V>>,
                               inp_prog: Transf<Em>)
                               -> (OptRef<'a,Assoc<&'a String,MemSlice<V>>>,Transf<Em>)
    where V : Bytes+Clone,Em : Embed {
    let off = prog.as_ref().threads.num_elem();
    let sz = prog.as_ref().global.num_elem();
    let glb = match prog {
        OptRef::Ref(ref rprog) => OptRef::Ref(&rprog.global),
        OptRef::Owned(rprog) => OptRef::Owned(rprog.global)
    };
    let glb_inp = Transformation::view(off,sz,inp_prog);
    (glb,glb_inp)
}

fn program_get_heap<'a,V,Em>(prog: OptRef<'a,Program<'a,V>>,
                             inp_prog: Transf<Em>)
                             -> (OptRef<'a,Assoc<InstructionRef<'a>,Vec<MemSlice<V>>>>,Transf<Em>)
    where V : Bytes+Clone,Em : Embed {
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
    where V : Bytes + Clone,Em : Embed {
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
    where V : Bytes + Clone,Em : Embed {
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
impl<'b,V : Bytes + Clone> Composite for Program<'b,V> {
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
