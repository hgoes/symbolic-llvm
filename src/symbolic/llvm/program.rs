use smtrs::composite::*;
use smtrs::composite::map::*;
use smtrs::composite::singleton::*;
use smtrs::composite::choice::*;
use smtrs::composite::vec::*;
use smtrs::embed::{Embed,DeriveConst,DeriveValues};
use super::mem::{Bytes,FromConst,MemSlice};
use super::{InstructionRef};
use super::thread::*;
use super::frame::*;
//use super::pointer::{Pointer,PointerTrg,Offset};
//use super::error::{Error,Errors,add_error};
use std::marker::PhantomData;
use num_bigint::{BigInt,BigUint};
use std::ops::Range;
use std::cmp::Ordering;
use std::hash::{Hash,Hasher};
use std::fmt;
use std::fmt::Debug;
use llvm_ir::datalayout::{DataLayout};

pub const STEP_BW: usize = 32;

pub type ThreadId<'a> = (Option<InstructionRef<'a>>,&'a String);

pub type Threads<'a,V> = Assoc<ThreadId<'a>,
                               CompVec<Thread<'a,V>>>;

pub type Globals<'a,V> = Assoc<&'a String,MemSlice<'a,V>>;

pub type Heap<'a,V> = Assoc<InstructionRef<'a>,CompVec<MemSlice<'a,V>>>;

pub type Aux = Choice<Data<Vec<Vec<u8>>>>;

pub type Step<'a> = Choice<(Data<ThreadId<'a>>,
                            SingletonBitVec)>;

pub type Nondet<'a,V> = Assoc<InstructionRef<'a>,V>;

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub struct Program<'a,V> {
    pub threads: Threads<'a,V>,
    pub global: Globals<'a,V>,
    pub heap: Heap<'a,V>,
    pub aux: Aux
}

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub struct ProgramInput<'a,V> {
    step: Step<'a>,
    nondet: Nondet<'a,V>
}

#[derive(PartialEq,Eq,Debug)]
pub struct ThreadsPath<'a,V: 'a>(PhantomData<&'a V>);

impl<'a,V: 'a> Clone for ThreadsPath<'a,V> {
    fn clone(&self) -> Self {
        ThreadsPath(PhantomData)
    }
}

#[derive(PartialEq,Eq,Debug)]
pub struct GlobalsPath<'a,V: 'a>(PhantomData<&'a V>);

impl<'a,V: 'a> Clone for GlobalsPath<'a,V> {
    fn clone(&self) -> Self {
        GlobalsPath(PhantomData)
    }
}

#[derive(PartialEq,Eq,Debug)]
pub struct HeapPath<'a,V: 'a>(PhantomData<&'a V>);

impl<'a,V: 'a> Clone for HeapPath<'a,V> {
    fn clone(&self) -> Self {
        HeapPath(PhantomData)
    }
}

#[derive(PartialEq,Eq,Debug)]
pub struct AuxPath<'a,V: 'a>(PhantomData<&'a V>);

impl<'a,V: 'a> Clone for AuxPath<'a,V> {
    fn clone(&self) -> Self {
        AuxPath(PhantomData)
    }
}

#[derive(PartialEq,Eq,Debug)]
pub struct StepPath<'a,V: 'a>(PhantomData<&'a V>);

impl<'a,V: 'a> Clone for StepPath<'a,V> {
    fn clone(&self) -> Self {
        StepPath(PhantomData)
    }
}

#[derive(PartialEq,Eq,Debug)]
pub struct NondetPath<'a,V: 'a>(PhantomData<&'a V>);

impl<'a,V: 'a> Clone for NondetPath<'a,V> {
    fn clone(&self) -> Self {
        NondetPath(PhantomData)
    }
}

impl<'a,V: Bytes<'a>+FromConst<'a>> Program<'a,V> {
    pub fn new<Em: Embed>(inp: &mut Vec<Em::Expr>,em: &mut Em) -> Result<Self,Em::Error> {
        Ok(Program { threads: Assoc::empty(inp,em)?,
                     global: Assoc::empty(inp,em)?,
                     heap: Assoc::empty(inp,em)?,
                     aux: Choice::empty(inp,em)? })
    }
    pub fn is_single_threaded(&self) -> bool {
        match self.threads.is_single() {
            None => false,
            Some(&(_,_,ref thrs)) => thrs.len()==1
        }
    }
    pub fn threads() -> ThreadsPath<'a,V> {
        ThreadsPath(PhantomData)
    }
    pub fn globals() -> GlobalsPath<'a,V> {
        GlobalsPath(PhantomData)
    }
    pub fn heap() -> HeapPath<'a,V> {
        HeapPath(PhantomData)
    }
    pub fn aux() -> AuxPath<'a,V> {
        AuxPath(PhantomData)
    }
}

impl<'a,V> ProgramInput<'a,V> {
    pub fn step() -> StepPath<'a,V> {
        StepPath(PhantomData)
    }
    pub fn nondet() -> NondetPath<'a,V> {
        NondetPath(PhantomData)
    }
}

impl<'a,V> SimplePathEl<'a> for ThreadsPath<'a,V> {
    type From = Program<'a,V>;
    type To   = Threads<'a,V>;
    fn get<'b>(&self,obj: &'b Self::From)
               -> &'b Self::To where 'a: 'b {
        &obj.threads
    }
    fn get_mut<'c>(&self,from: &'c mut Self::From)
                   -> &'c mut Self::To where 'a: 'c {
        &mut from.threads
    }
}

impl<'a,V,Em: Embed> PathEl<'a,Em> for ThreadsPath<'a,V> {
    fn read<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        prev_from: &Prev::From,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        prev.read(prev_from,pos,arr,em)
    }
    fn read_slice<'c,Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        prev_from: &Prev::From,
        pos: usize,
        len: usize,
        arr: &'c [Em::Expr])
        -> Option<&'c [Em::Expr]> {
        prev.read_slice(prev_from,pos,len,arr)
    }
    fn write<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        prev_from: &Prev::From,
        pos: usize,
        e: Em::Expr,
        arr: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        prev.write(prev_from,pos,e,arr,em)
    }
    fn write_slice<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        prev_from: &mut Prev::From,
        pos: usize,
        old_len: usize,
        src: &mut Vec<Em::Expr>,
        trg: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        prev.write_slice(prev_from,pos,old_len,src,trg,em)
    }
}

impl<'a,V: HasSorts> SimplePathEl<'a> for GlobalsPath<'a,V> {
    type From = Program<'a,V>;
    type To   = Globals<'a,V>;
    fn get<'b>(&self,obj: &'b Self::From)
               -> &'b Self::To where 'a: 'b {
        &obj.global
    }
    fn get_mut<'c>(&self,from: &'c mut Self::From)
                   -> &'c mut Self::To where 'a: 'c {
        &mut from.global
    }
}

impl<'a,V: HasSorts,Em: Embed> PathEl<'a,Em> for GlobalsPath<'a,V> {
    fn read<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        prev_from: &Prev::From,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        let off = prev.get(prev_from).threads.num_elem();
        prev.read(prev_from,pos+off,arr,em)
    }
    fn read_slice<'c,Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        prev_from: &Prev::From,
        pos: usize,
        len: usize,
        arr: &'c [Em::Expr])
        -> Option<&'c [Em::Expr]> {
        let off = prev.get(prev_from).threads.num_elem();
        prev.read_slice(prev_from,pos+off,len,arr)
    }
    fn write<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        prev_from: &Prev::From,
        pos: usize,
        e: Em::Expr,
        arr: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        let off = prev.get(prev_from).threads.num_elem();
        prev.write(prev_from,pos+off,e,arr,em)
    }
    fn write_slice<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        prev_from: &mut Prev::From,
        pos: usize,
        old_len: usize,
        src: &mut Vec<Em::Expr>,
        trg: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        let off = prev.get(prev_from).threads.num_elem();
        prev.write_slice(prev_from,pos+off,old_len,src,trg,em)
    }
}

impl<'a,V: HasSorts> SimplePathEl<'a> for HeapPath<'a,V> {
    type From = Program<'a,V>;
    type To   = Heap<'a,V>;
    fn get<'b>(&self,obj: &'b Self::From)
               -> &'b Self::To where 'a: 'b {
        &obj.heap
    }
    fn get_mut<'c>(&self,from: &'c mut Self::From)
                   -> &'c mut Self::To where 'a: 'c {
        &mut from.heap
    }
}

impl<'a,V: HasSorts,Em: Embed> PathEl<'a,Em> for HeapPath<'a,V> {
    fn read<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        prev_from: &Prev::From,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        let off = {
            let prog = prev.get(prev_from);
            prog.threads.num_elem() +
                prog.global.num_elem()
        };
        prev.read(prev_from,pos+off,arr,em)
    }
    fn read_slice<'c,Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        prev_from: &Prev::From,
        pos: usize,
        len: usize,
        arr: &'c [Em::Expr])
        -> Option<&'c [Em::Expr]> {
        let off = {
            let prog = prev.get(prev_from);
            prog.threads.num_elem() +
                prog.global.num_elem()
        };
        prev.read_slice(prev_from,pos+off,len,arr)
    }
    fn write<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        prev_from: &Prev::From,
        pos: usize,
        e: Em::Expr,
        arr: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        let off = {
            let prog = prev.get(prev_from);
            prog.threads.num_elem() +
                prog.global.num_elem()
        };
        prev.write(prev_from,pos+off,e,arr,em)
    }
    fn write_slice<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        prev_from: &mut Prev::From,
        pos: usize,
        old_len: usize,
        src: &mut Vec<Em::Expr>,
        trg: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        let off = {
            let prog = prev.get(prev_from);
            prog.threads.num_elem() +
                prog.global.num_elem()
        };
        prev.write_slice(prev_from,pos+off,old_len,src,trg,em)
    }
}

impl<'a,V: HasSorts> SimplePathEl<'a> for AuxPath<'a,V> {
    type From = Program<'a,V>;
    type To   = Aux;
    fn get<'b>(&self,obj: &'b Self::From)
               -> &'b Self::To where 'a: 'b {
        &obj.aux
    }
    fn get_mut<'c>(&self,from: &'c mut Self::From)
                   -> &'c mut Self::To where 'a: 'c {
        &mut from.aux
    }
}

impl<'a,V: HasSorts,Em: Embed> PathEl<'a,Em> for AuxPath<'a,V> {
    fn read<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        prev_from: &Prev::From,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        let off = {
            let prog = prev.get(prev_from);
            prog.threads.num_elem() +
                prog.global.num_elem() +
                prog.heap.num_elem()
        };
        prev.read(prev_from,pos+off,arr,em)
    }
    fn read_slice<'c,Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        prev_from: &Prev::From,
        pos: usize,
        len: usize,
        arr: &'c [Em::Expr])
        -> Option<&'c [Em::Expr]> {
        let off = {
            let prog = prev.get(prev_from);
            prog.threads.num_elem() +
                prog.global.num_elem() +
                prog.heap.num_elem()
        };
        prev.read_slice(prev_from,pos+off,len,arr)
    }
    fn write<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        prev_from: &Prev::From,
        pos: usize,
        e: Em::Expr,
        arr: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        let off = {
            let prog = prev.get(prev_from);
            prog.threads.num_elem() +
                prog.global.num_elem() +
                prog.heap.num_elem()
        };
        prev.write(prev_from,pos+off,e,arr,em)
    }
    fn write_slice<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        prev_from: &mut Prev::From,
        pos: usize,
        old_len: usize,
        src: &mut Vec<Em::Expr>,
        trg: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        let off = {
            let prog = prev.get(prev_from);
            prog.threads.num_elem() +
                prog.global.num_elem() +
                prog.heap.num_elem()
        };
        prev.write_slice(prev_from,pos+off,old_len,src,trg,em)
    }
}

impl<'a,V> SimplePathEl<'a> for StepPath<'a,V> {
    type From = ProgramInput<'a,V>;
    type To   = Step<'a>;
    fn get<'b>(&self,obj: &'b Self::From)
               -> &'b Self::To where 'a: 'b {
        &obj.step
    }
    fn get_mut<'c>(&self,from: &'c mut Self::From)
                   -> &'c mut Self::To where 'a: 'c {
        &mut from.step
    }
}

impl<'a,V,Em: Embed> PathEl<'a,Em> for StepPath<'a,V> {
    fn read<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        prev_from: &Prev::From,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        prev.read(prev_from,pos,arr,em)
    }
    fn read_slice<'c,Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        prev_from: &Prev::From,
        pos: usize,
        len: usize,
        arr: &'c [Em::Expr])
        -> Option<&'c [Em::Expr]> {
        prev.read_slice(prev_from,pos,len,arr)
    }
    fn write<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        prev_from: &Prev::From,
        pos: usize,
        e: Em::Expr,
        arr: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        prev.write(prev_from,pos,e,arr,em)
    }
    fn write_slice<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        prev_from: &mut Prev::From,
        pos: usize,
        old_len: usize,
        src: &mut Vec<Em::Expr>,
        trg: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        prev.write_slice(prev_from,pos,old_len,src,trg,em)
    }
}

impl<'a,V: HasSorts> SimplePathEl<'a> for NondetPath<'a,V> {
    type From = ProgramInput<'a,V>;
    type To   = Nondet<'a,V>;
    fn get<'b>(&self,obj: &'b Self::From)
               -> &'b Self::To where 'a: 'b {
        &obj.nondet
    }
    fn get_mut<'c>(&self,from: &'c mut Self::From)
                   -> &'c mut Self::To where 'a: 'c {
        &mut from.nondet
    }
}

impl<'a,V: HasSorts,Em: Embed> PathEl<'a,Em> for NondetPath<'a,V> {
    fn read<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        prev_from: &Prev::From,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        let off = prev.get(prev_from).step.num_elem();
        prev.read(prev_from,pos+off,arr,em)
    }
    fn read_slice<'c,Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        prev_from: &Prev::From,
        pos: usize,
        len: usize,
        arr: &'c [Em::Expr])
        -> Option<&'c [Em::Expr]> {
        let off = prev.get(prev_from).step.num_elem();
        prev.read_slice(prev_from,pos+off,len,arr)
    }
    fn write<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        prev_from: &Prev::From,
        pos: usize,
        e: Em::Expr,
        arr: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        let off = prev.get(prev_from).step.num_elem();
        prev.write(prev_from,pos+off,e,arr,em)
    }
    fn write_slice<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        prev_from: &mut Prev::From,
        pos: usize,
        old_len: usize,
        src: &mut Vec<Em::Expr>,
        trg: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        let off = prev.get(prev_from).step.num_elem();
        prev.write_slice(prev_from,pos+off,old_len,src,trg,em)
    }
}

/*
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
                                                   _: &mut Em)
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
        },
        &PointerTrg::Aux(_) => unimplemented!(),
        &PointerTrg::AuxArray => unimplemented!()
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
                              inp_heap: Transf<Em>,
                              aux: OptRef<'a,Aux>,
                              inp_aux: Transf<Em>)
                              -> (OptRef<'c,Program<'b,V>>,Transf<Em>)
    where V : Bytes+FromConst<'b>+Clone,Em : Embed {
    debug_assert_eq!(thrs.as_ref().num_elem(),inp_thrs.size());
    debug_assert_eq!(glob.as_ref().num_elem(),inp_glob.size());
    debug_assert_eq!(heap.as_ref().num_elem(),inp_heap.size());
    debug_assert_eq!(aux.as_ref().num_elem(),inp_aux.size());

    let prog = Program { threads: thrs.as_obj(),
                         global: glob.as_obj(),
                         heap: heap.as_obj(),
                         aux: aux.as_obj() };
    let prog_inp = Transformation::concat(&[inp_thrs,inp_glob,inp_heap,inp_aux]);
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
                                         Transf<Em>,
                                         OptRef<'a,Aux>,
                                         Transf<Em>)
    where V : Bytes+FromConst<'b>+Clone,Em : Embed {
    let (thrs,glob,hp,aux) = match prog {
        OptRef::Ref(ref prog)
            => (OptRef::Ref(&prog.threads),
                OptRef::Ref(&prog.global),
                OptRef::Ref(&prog.heap),
                OptRef::Ref(&prog.aux)),
        OptRef::Owned(prog)
            => (OptRef::Owned(prog.threads),
                OptRef::Owned(prog.global),
                OptRef::Owned(prog.heap),
                OptRef::Owned(prog.aux))
    };
    let sz_thrs = thrs.as_ref().num_elem();
    let sz_glob = glob.as_ref().num_elem();
    let sz_hp = hp.as_ref().num_elem();
    let sz_aux = aux.as_ref().num_elem();
    let inp_thrs = Transformation::view(0,sz_thrs,inp_prog.clone());
    let inp_glob = Transformation::view(sz_thrs,sz_glob,inp_prog.clone());
    let inp_hp = Transformation::view(sz_thrs+sz_glob,sz_hp,inp_prog.clone());
    let inp_aux = Transformation::view(sz_thrs+sz_glob+sz_hp,sz_aux,inp_prog);
    (thrs,inp_thrs,glob,inp_glob,hp,inp_hp,aux,inp_aux)
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
}*/

impl<'b,V: HasSorts> HasSorts for Program<'b,V> {
    fn num_elem(&self) -> usize {
        self.threads.num_elem() +
            self.global.num_elem() +
            self.heap.num_elem() +
            self.aux.num_elem()
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
        let off3 = off2+self.heap.num_elem();
        if pos < off3 {
            return self.heap.elem_sort(pos-off2,em)
        }
        debug_assert!({ let off4 = off2+self.aux.num_elem();
                        pos < off4 });
        self.aux.elem_sort(pos-off3,em)
    }
}

impl<'a,V: Bytes<'a>+FromConst<'a>+Debug> Composite<'a> for Program<'a,V> {
    fn combine<Em,PL,PR,FComb,FL,FR>(
        pl: &PL,froml: &PL::From,arrl: &[Em::Expr],
        pr: &PR,fromr: &PR::From,arrr: &[Em::Expr],
        comb: &FComb,only_l: &FL,only_r: &FR,
        res: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<Option<Self>,Em::Error>
        where
        Em: Embed,
        PL: Path<'a,Em,To=Self>,
        PR: Path<'a,Em,To=Self>,
        FComb: Fn(Em::Expr,Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
        FL: Fn(Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
        FR: Fn(Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error> {

        let thr_l = pl.clone().then(Self::threads());
        let thr_r = pr.clone().then(Self::threads());

        let nthr = match Threads::combine(&thr_l,froml,arrl,
                                          &thr_r,fromr,arrr,
                                          comb,only_l,only_r,
                                          res,em)? {
            None => return Ok(None),
            Some(r) => r
        };

        let glb_l = pl.clone().then(Self::globals());
        let glb_r = pr.clone().then(Self::globals());

        let nglb = match Globals::combine(&glb_l,froml,arrl,
                                          &glb_r,fromr,arrr,
                                          comb,only_l,only_r,
                                          res,em)? {
            None => return Ok(None),
            Some(r) => r
        };
        
        let hp_l = pl.clone().then(Self::heap());
        let hp_r = pr.clone().then(Self::heap());
        
        let nhp = match Heap::combine(&hp_l,froml,arrl,
                                      &hp_r,fromr,arrr,
                                      comb,only_l,only_r,
                                      res,em)? {
            None => return Ok(None),
            Some(r) => r
        };

        let aux_l = pl.clone().then(Self::aux());
        let aux_r = pr.clone().then(Self::aux());
        
        let naux = match Aux::combine(&aux_l,froml,arrl,
                                      &aux_r,fromr,arrr,
                                      comb,only_l,only_r,
                                      res,em)? {
            None => return Ok(None),
            Some(r) => r
        };
        
        Ok(Some(Program { threads: nthr,
                          global: nglb,
                          heap: nhp,
                          aux: naux }))
    }
}

impl<'b,V: HasSorts> HasSorts for ProgramInput<'b,V> {
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
}

impl<'a,V: Bytes<'a>> Composite<'a> for ProgramInput<'a,V> {
    fn combine<Em,PL,PR,FComb,FL,FR>(
        pl: &PL,froml: &PL::From,arrl: &[Em::Expr],
        pr: &PR,fromr: &PR::From,arrr: &[Em::Expr],
        comb: &FComb,only_l: &FL,only_r: &FR,
        res: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<Option<Self>,Em::Error>
        where
        Em: Embed,
        PL: Path<'a,Em,To=Self>,
        PR: Path<'a,Em,To=Self>,
        FComb: Fn(Em::Expr,Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
        FL: Fn(Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
        FR: Fn(Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error> {

        let step_l = pl.clone().then(Self::step());
        let step_r = pr.clone().then(Self::step());

        let nstep = match Step::combine(&step_l,froml,arrl,
                                        &step_r,fromr,arrr,
                                        comb,only_l,only_r,
                                        res,em)? {
            None => return Ok(None),
            Some(r) => r
        };

        let nd_l = pl.clone().then(Self::nondet());
        let nd_r = pr.clone().then(Self::nondet());

        let nnd = match Nondet::combine(&nd_l,froml,arrl,
                                        &nd_r,fromr,arrr,
                                        comb,only_l,only_r,
                                        res,em)? {
            None => return Ok(None),
            Some(r) => r
        };

        Ok(Some(ProgramInput { step: nstep,
                               nondet: nnd }))
    }
}
/*
pub struct CurrentThreadIter<'a,V,Em : DeriveValues> {
    phantom: PhantomData<V>,
    step: Option<Transf<Em>>,
    thr_id: ThreadId<'a>,
    iter: IndexedIter<Em>
}

impl<'a,Em : DeriveValues,V : 'a+Bytes+FromConst<'a>+Clone
     > CurrentThreadIter<'a,V,Em> {
    pub fn new(prog: &Program<'a,V>,
               thr_id: ThreadId<'a>,
               step: Option<Transf<Em>>,
               thr_idx: Transf<Em>,
               exprs: &[Em::Expr],
               em: &mut Em) -> Result<CurrentThreadIter<'a,V,Em>,Em::Error> {
        Ok(CurrentThreadIter {
            phantom: PhantomData,
            step: step,
            thr_id: thr_id,
            iter: access_dyn(prog.threads.access(&thr_id).1,thr_idx,exprs,em)?
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
    let e = em.const_bitvec(bw,BigUint::from(vec.idx))?;
    let inp = Transformation::constant(vec![e]);
    Ok((assoc.key.clone(),inp))
}

impl<'a,Em : DeriveValues,V : 'a> CondIterator<Em> for CurrentThreadIter<'a,V,Em> {
    type Item = ThreadView<'a,V>;
    fn next(&mut self,conds: &mut Vec<Transf<Em>>,pos: usize,em: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        if conds.len()==pos {
            if let Some(ref step_) = self.step {
                conds.push(step_.clone());
            }
        }
        match self.iter.next(conds,pos+1,em)? {
            None => Ok(None),
            Some(i) => Ok(Some(Then::new(ThreadsView::new(),
                                         Then::new(AssocView::new(self.thr_id.clone()),
                                                   VecView::new(i)))))
        }
    }
}

type TopFrameIdIter<'a,'b,It,V,Em>
    = SeqPure<It,Context<GetterElement<'b,Choice<Data<Option<ContextId<'a>>>>,
                                       Chosen<'b,Data<Option<ContextId<'a>>>,Em>>,ThreadView<'a,V>>,
              (&'b Program<'a,V>,
               Transf<Em>),
              fn(&(&'b Program<'a,V>,
                   Transf<Em>),
                 ThreadView<'a,V>) -> Context<GetterElement<'b,Choice<Data<Option<ContextId<'a>>>>,
                                                            Chosen<'b,Data<Option<ContextId<'a>>>,Em>>,ThreadView<'a,V>>>;

pub fn get_frame_id_iter<'a,'b,V,Em>(ctx: &(&'b Program<'a,V>,
                                            Transf<Em>),
                                     thr_view: ThreadView<'a,V>)
                                     -> Context<GetterElement<'b,Choice<Data<Option<ContextId<'a>>>>,
                                                              Chosen<'b,Data<Option<ContextId<'a>>>,Em>>,ThreadView<'a,V>>
    where Em : Embed, V : Bytes+FromConst<'a> {
    
    let (top_off,top) = thr_view.clone().then(StackTopView::new()).get_el_ext(ctx.0);
    let top_inp = Transformation::view(top_off,top.num_elem(),ctx.1.clone());
    top.chosen(top_inp).get_element(top).context(thr_view)
}


pub fn top_frame_id_iter<'a,'b,V,It,Em>(prog: &'b Program<'a,V>,
                                        prog_inp: Transf<Em>,
                                        prev: It) -> TopFrameIdIter<'a,'b,It,V,Em>
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
        ContextId::Stack(_,instr) => {
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
                                        VecView<MemSlice<'a,V>>>>>>>>),
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

impl<'a,V> ViewMut for PointerView<'a,V>
    where V : 'a+Bytes+FromConst<'a> {
    fn get_el_mut<'b>(&self, obj: &'b mut Self::Viewed) -> &'b mut Self::Element
        where Self : 'b {
        match self {
            &PointerView::Global(ref view)
                => view.get_el_mut(obj),
            &PointerView::Heap(ref view)
                => view.get_el_mut(obj),
            &PointerView::Stack(ref view)
                => view.get_el_mut(obj)
        }
    }
    fn get_el_mut_ext<'b>(&self,obj: &'b mut Self::Viewed)
                          -> (usize, &'b mut Self::Element)
        where
        Self : 'b {
        match self {
            &PointerView::Global(ref view)
                => view.get_el_mut_ext(obj),
            &PointerView::Heap(ref view)
                => view.get_el_mut_ext(obj),
            &PointerView::Stack(ref view)
                => view.get_el_mut_ext(obj)
        }
    }
}

#[derive(Clone)]
pub enum ProgramMeaning<'b,V : Semantic+Bytes+FromConst<'b>> {
    Threads(<Threads<'b,V> as Semantic>::Meaning),
    Global(<Globals<'b,V> as Semantic>::Meaning),
    Heap(<Heap<'b,V> as Semantic>::Meaning),
    Aux(<Aux as Semantic>::Meaning)
}

pub enum ProgramMeaningCtx<'b,V : Semantic+Bytes+FromConst<'b>> {
    Threads(<Threads<'b,V> as Semantic>::MeaningCtx),
    Global(<Globals<'b,V> as Semantic>::MeaningCtx),
    Heap(<Heap<'b,V> as Semantic>::MeaningCtx),
    Aux(<Aux as Semantic>::MeaningCtx)
}

impl<'b,V : Semantic+Bytes+FromConst<'b>> PartialEq for ProgramMeaning<'b,V> {
    fn eq(&self,other: &ProgramMeaning<'b,V>) -> bool {
        match self {
            &ProgramMeaning::Threads(ref p) => match other {
                &ProgramMeaning::Threads(ref q) => p.eq(q),
                _ => false
            },
            &ProgramMeaning::Global(ref p) => match other {
                &ProgramMeaning::Global(ref q) => p.eq(q),
                _ => false
            },
            &ProgramMeaning::Heap(ref p) => match other {
                &ProgramMeaning::Heap(ref q) => p.eq(q),
                _ => false
            },
            &ProgramMeaning::Aux(ref p) => match other {
                &ProgramMeaning::Aux(ref q) => p.eq(q),
                _ => false
            }
        }
    }
}

impl<'b,V : Semantic+Bytes+FromConst<'b>> Eq for ProgramMeaning<'b,V> {}

impl<'b,V : Semantic+Bytes+FromConst<'b>> PartialOrd for ProgramMeaning<'b,V> {
    fn partial_cmp(&self,other: &ProgramMeaning<'b,V>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<'b,V : Semantic+Bytes+FromConst<'b>> Ord for ProgramMeaning<'b,V> {
    fn cmp(&self,other: &ProgramMeaning<'b,V>) -> Ordering {
        match (self,other) {
            (&ProgramMeaning::Threads(ref p),
             &ProgramMeaning::Threads(ref q)) => p.cmp(q),
            (&ProgramMeaning::Threads(_),_) => Ordering::Less,
            (_,&ProgramMeaning::Threads(_)) => Ordering::Greater,
            (&ProgramMeaning::Global(ref p),
             &ProgramMeaning::Global(ref q)) => p.cmp(q),
            (&ProgramMeaning::Global(_),_) => Ordering::Less,
            (_,&ProgramMeaning::Global(_)) => Ordering::Greater,
            (&ProgramMeaning::Heap(ref p),
             &ProgramMeaning::Heap(ref q)) => p.cmp(q),
            (&ProgramMeaning::Heap(ref p),_) => Ordering::Less,
            (_,&ProgramMeaning::Heap(ref p)) => Ordering::Greater,
            (&ProgramMeaning::Aux(ref p),
             &ProgramMeaning::Aux(ref q)) => p.cmp(q)
        }
    }
}

impl<'b,V : Semantic+Bytes+FromConst<'b>> Hash for ProgramMeaning<'b,V> {
    fn hash<H>(&self, state: &mut H) where H: Hasher {
        match self {
            &ProgramMeaning::Threads(ref p) => {
                (0 as u8).hash(state);
                p.hash(state);
            },
            &ProgramMeaning::Global(ref p) => {
                (1 as u8).hash(state);
                p.hash(state);
            },
            &ProgramMeaning::Heap(ref p) => {
                (2 as u8).hash(state);
                p.hash(state);
            },
            &ProgramMeaning::Aux(ref p) => {
                (3 as u8).hash(state);
                p.hash(state)
            }
        }
    }
}

impl<'b,V : Semantic+Bytes+FromConst<'b>> fmt::Debug for ProgramMeaning<'b,V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            &ProgramMeaning::Threads(ref p) => f.debug_tuple("Threads")
                .field(p).finish(),
            &ProgramMeaning::Global(ref p) => f.debug_tuple("Global")
                .field(p).finish(),
            &ProgramMeaning::Heap(ref p) => f.debug_tuple("Heap")
                .field(p).finish(),
            &ProgramMeaning::Aux(ref p) => f.debug_tuple("Aux")
                .field(p).finish()
        }
    }
}


impl<'b,V : Semantic+Bytes+FromConst<'b>> ProgramMeaning<'b,V> {
    pub fn is_pc(&self) -> bool {
        match self {
            &ProgramMeaning::Threads(ref m) => m.meaning.meaning.is_pc(),
            _ => false
        }
    }
}

impl<'b,V : Semantic+Bytes+FromConst<'b>> Semantic for Program<'b,V> {
    type Meaning = ProgramMeaning<'b,V>;
    type MeaningCtx = ProgramMeaningCtx<'b,V>;
    fn meaning(&self,pos: usize) -> Self::Meaning {
        let off1 = self.threads.num_elem();
        if pos<off1 {
            return ProgramMeaning::Threads(self.threads.meaning(pos))
        }
        let off2 = off1+self.global.num_elem();
        if pos<off2 {
            return ProgramMeaning::Global(self.global.meaning(pos-off1))
        }
        let off3 = off2+self.heap.num_elem();
        if pos<off3 {
            return ProgramMeaning::Heap(self.heap.meaning(pos-off2))
        }
        return ProgramMeaning::Aux(self.aux.meaning(pos-off3))
    }
    fn fmt_meaning<F : fmt::Write>(&self,m: &Self::Meaning,fmt: &mut F) -> Result<(),fmt::Error> {
        match m {
            &ProgramMeaning::Threads(ref nm) => {
                write!(fmt,"threads.")?;
                self.threads.fmt_meaning(nm,fmt)
            },
            &ProgramMeaning::Global(ref nm) => {
                write!(fmt,"global.")?;
                self.global.fmt_meaning(nm,fmt)
            },
            &ProgramMeaning::Heap(ref nm) => {
                write!(fmt,"heap.")?;
                self.heap.fmt_meaning(nm,fmt)
            },
            &ProgramMeaning::Aux(ref nm) => {
                write!(fmt,"aux.")?;
                self.aux.fmt_meaning(nm,fmt)
            }
        }
    }
    fn first_meaning(&self) -> Option<(Self::MeaningCtx,Self::Meaning)> {
        if let Some((ctx,m)) = self.threads.first_meaning() {
            Some((ProgramMeaningCtx::Threads(ctx),
                  ProgramMeaning::Threads(m)))
        } else if let Some((ctx,m)) = self.global.first_meaning() {
            Some((ProgramMeaningCtx::Global(ctx),
                  ProgramMeaning::Global(m)))
        } else if let Some((ctx,m)) = self.heap.first_meaning() {
            Some((ProgramMeaningCtx::Heap(ctx),
                  ProgramMeaning::Heap(m)))
        } else if let Some((ctx,m)) = self.aux.first_meaning() {
            Some((ProgramMeaningCtx::Aux(ctx),
                  ProgramMeaning::Aux(m)))
        } else {
            None
        }
    }
    fn next_meaning(&self,ctx: &mut Self::MeaningCtx,m: &mut Self::Meaning) -> bool {
        let (nctx,nm) = match ctx {
            &mut ProgramMeaningCtx::Threads(ref mut cctx) => match m {
                &mut ProgramMeaning::Threads(ref mut cm) => if self.threads.next_meaning(cctx,cm) {
                    return true
                } else if let Some((nctx,nm)) = self.global.first_meaning() {
                    (ProgramMeaningCtx::Global(nctx),
                     ProgramMeaning::Global(nm))
                } else if let Some((nctx,nm)) = self.heap.first_meaning() {
                    (ProgramMeaningCtx::Heap(nctx),
                     ProgramMeaning::Heap(nm))
                } else if let Some((nctx,nm)) = self.aux.first_meaning() {
                    (ProgramMeaningCtx::Aux(nctx),
                     ProgramMeaning::Aux(nm))
                } else {
                    return false
                },
                _ => unreachable!()
            },
            &mut ProgramMeaningCtx::Global(ref mut cctx) => match m {
                &mut ProgramMeaning::Global(ref mut cm) => if self.global.next_meaning(cctx,cm) {
                    return true
                } else if let Some((nctx,nm)) = self.heap.first_meaning() {
                    (ProgramMeaningCtx::Heap(nctx),
                     ProgramMeaning::Heap(nm))
                } else if let Some((nctx,nm)) = self.aux.first_meaning() {
                    (ProgramMeaningCtx::Aux(nctx),
                     ProgramMeaning::Aux(nm))
                } else {
                    return false
                },
                _ => unreachable!()
            },
            &mut ProgramMeaningCtx::Heap(ref mut cctx) => match m {
                &mut ProgramMeaning::Heap(ref mut cm) => if self.heap.next_meaning(cctx,cm) {
                    return true
                } else if let Some((nctx,nm)) = self.aux.first_meaning() {
                    (ProgramMeaningCtx::Aux(nctx),
                     ProgramMeaning::Aux(nm))
                } else {
                    return false
                },
                _ => unreachable!()
            },
            &mut ProgramMeaningCtx::Aux(ref mut cctx) => match m {
                &mut ProgramMeaning::Aux(ref mut cm) => return self.aux.next_meaning(cctx,cm),
                _ => unreachable!()
            }
        };
        *ctx = nctx;
        *m = nm;
        true
    }
}

pub enum MemLookup<'a,V : 'a> {
    Slice(PointerView<'a,V>),
    Aux(usize),
    AuxArray
}

pub enum MemLookups<'a : 'b,'b,V : 'a,Em : DeriveValues>
    where Em::Expr : 'b {
    Global(Option<&'a String>,PhantomData<V>),
    Heap(InstructionRef<'a>,IndexedIter<Em>),
    StackStart(&'b Program<'a,V>,
               ThreadId<'a>,Transf<Em>,
               FrameId<'a>,Transf<Em>,
               InstructionRef<'a>,Transf<Em>,
               &'b [Em::Expr]),
    Stack(StackLookups<'a,'b,V,Em>),
    Aux(usize),
    AuxArray,
    End
}

pub struct StackLookups<'a : 'b,'b,V : 'a,Em : DeriveValues>
    where Em::Expr : 'b {
    program: &'b Program<'a,V>,
    thread_id: ThreadId<'a>,
    thread_iter: IndexedIter<Em>,
    thread_last: usize,
    thread_pos: usize,
    frame_id: FrameId<'a>,
    frame_index: Transf<Em>,
    frame_iter: IndexedIter<Em>,
    frame_last: usize,
    frame_pos: usize,
    instr_id: InstructionRef<'a>,
    instr_index: Transf<Em>,
    instr_iter: IndexedIter<Em>,
    exprs: &'b [Em::Expr]
}

impl<'a : 'b,'b,V : 'a+Bytes+FromConst<'a>+Debug,Em : DeriveValues> StackLookups<'a,'b,V,Em>
    where Em::Expr : 'b {
    fn new(program: &'b Program<'a,V>,
           thread_id: ThreadId<'a>,
           thread_index: Transf<Em>,
           frame_id: FrameId<'a>,
           frame_index: Transf<Em>,
           instr_id: InstructionRef<'a>,
           instr_index: Transf<Em>,
           exprs: &'b [Em::Expr],
           conds: &mut Vec<Transf<Em>>,
           pos: usize,
           em: &mut Em) -> Result<Option<Self>,Em::Error> {
        let view = ThreadsView::new()
            .then(AssocView::new(thread_id));
        let pool = view.get_el(program);
        /*{ // Debugging
            let frame_idx_ = frame_index.get(exprs,0,em)?;
            println!("ACCESS DYN {:?}, {:?}",pool,match em.derive_values(&frame_idx_)? {
                None => vec![],
                Some(it) => it.collect::<Vec<_>>()
            });
        }*/
        let mut thread_iter = access_dyn(pool,thread_index,exprs,em)?;
        while let Some(thread_last) = thread_iter.next(conds,pos,em)? {
            let thread_pos = conds.len();
            let mut frame_iter = Self::get_frame_iter(program,
                                                      thread_id.clone(),
                                                      thread_last,
                                                      frame_id.clone(),
                                                      frame_index.clone(),
                                                      exprs,em)?;
            while let Some(frame_last) = frame_iter.next(conds,thread_pos,em)? {
                let frame_pos = conds.len();
                let instr_iter = Self::get_instr_iter(program,
                                                      thread_id.clone(),
                                                      thread_last,
                                                      frame_id.clone(),
                                                      frame_last,
                                                      instr_id.clone(),
                                                      instr_index.clone(),
                                                      exprs,em)?;
                return Ok(Some(StackLookups { program: program,
                                              thread_id: thread_id,
                                              thread_iter: thread_iter,
                                              thread_last: thread_last,
                                              thread_pos: thread_pos,
                                              frame_id: frame_id,
                                              frame_index: frame_index,
                                              frame_iter: frame_iter,
                                              frame_last: frame_last,
                                              frame_pos: frame_pos,
                                              instr_id: instr_id,
                                              instr_index: instr_index,
                                              instr_iter: instr_iter,
                                              exprs: exprs }))
            }
        }
        Ok(None)
    }
    fn frame_view(frame_id: FrameId<'a>,
                  frame_last: usize) -> FrameView<'a,V> {
        match frame_id {
            FrameId::Call(cid) => FrameView::Call(
                CallStackView::new()
                    .then(AssocView::new(cid)
                          .then(BitVecVectorStackView::new(frame_last)
                                .then(SndView::new())))),
            FrameId::Stack(i) => FrameView::Stack(
                StackView::new()
                    .then(AssocView::new(i)
                          .then(BitVecVectorStackView::new(frame_last))))
        }
    }
    fn get_frame_iter(program: &Program<'a,V>,
                      thread_id: ThreadId<'a>,
                      thread_last: usize,
                      frame_id: FrameId<'a>,
                      frame_index: Transf<Em>,
                      exprs: &[Em::Expr],
                      em: &mut Em) -> Result<IndexedIter<Em>,Em::Error> {
        match frame_id {
            FrameId::Call(cid) => {
                let view = ThreadsView::new()
                    .then(AssocView::new(thread_id)
                          .then(VecView::new(thread_last)
                                .then(CallStackView::new()
                                      .then(AssocView::new(cid)))));
                let frs = view.get_el(program);
                Ok(frs.access(frame_index,exprs,em)?.iter)
            },
            FrameId::Stack(i) => {
                let view = ThreadsView::new()
                    .then(AssocView::new(thread_id)
                          .then(VecView::new(thread_last)
                                .then(StackView::new()
                                      .then(AssocView::new(i)))));
                let frs = view.get_el(program);
                Ok(frs.access(frame_index,exprs,em)?.iter)
            }
        }
    }
    fn get_instr_iter(program: &Program<'a,V>,
                      thread_id: ThreadId<'a>,
                      thread_last: usize,
                      frame_id: FrameId<'a>,
                      frame_last: usize,
                      instr_id: InstructionRef<'a>,
                      instr_index: Transf<Em>,
                      exprs: &[Em::Expr],
                      em: &mut Em) -> Result<IndexedIter<Em>,Em::Error> {
        let fr_view = Self::frame_view(frame_id,frame_last);
        let view = ThreadsView::new()
            .then(AssocView::new(thread_id)
                  .then(VecView::new(thread_last)
                        .then(fr_view
                              .then(AllocationsView::new()
                                    .then(AssocView::new(instr_id))))));
        let pool = view.get_el(program);
        access_dyn(pool,instr_index,exprs,em)
    }
    fn next_instr(&mut self,conds: &mut Vec<Transf<Em>>,em: &mut Em) -> Result<Option<usize>,Em::Error> {
        self.instr_iter.next(conds,self.frame_pos,em)
    }
    fn mk_view(&self,instr_last: usize) -> PointerView<'a,V> {
        let fr_view = match self.frame_id {
            FrameId::Call(ref cid) => FrameView::Call(
                CallStackView::new()
                    .then(AssocView::new(cid.clone())
                          .then(BitVecVectorStackView::new(self.frame_last)
                                .then(SndView::new())))),
            FrameId::Stack(ref i) => FrameView::Stack(
                StackView::new()
                    .then(AssocView::new(i.clone())
                          .then(BitVecVectorStackView::new(self.frame_last))))
        };
        PointerView::Stack(ThreadsView::new()
                           .then(AssocView::new(self.thread_id.clone())
                                 .then(VecView::new(self.thread_last)
                                       .then(fr_view
                                             .then(AllocationsView::new()
                                                   .then(AssocView::new(self.instr_id.clone())
                                                         .then(VecView::new(instr_last))))))))
    }
}

impl<'a : 'b,'b,V : 'a+Bytes+FromConst<'a>+Debug,Em : DeriveValues> CondIterator<Em> for StackLookups<'a,'b,V,Em> {
    type Item = PointerView<'a,V>;
    fn next(&mut self,conds: &mut Vec<Transf<Em>>,pos: usize,em: &mut Em) -> Result<Option<Self::Item>,Em::Error> {
        match self.instr_iter.next(conds,self.frame_pos,em)? {
            Some(instr_last) => Ok(Some(self.mk_view(instr_last))),
            None => {
                while let Some(frame_last) = self.frame_iter.next(conds,self.thread_pos,em)? {
                    let frame_pos = conds.len();
                    let mut instr_iter = Self::get_instr_iter(self.program,
                                                              self.thread_id.clone(),
                                                              self.thread_last,
                                                              self.frame_id.clone(),
                                                              frame_last,
                                                              self.instr_id.clone(),
                                                              self.instr_index.clone(),
                                                              self.exprs,em)?;
                    if let Some(instr_last) = instr_iter.next(conds,frame_pos,em)? {
                        self.frame_last = frame_last;
                        self.frame_pos = frame_pos;
                        self.instr_iter = instr_iter;
                        return Ok(Some(self.mk_view(instr_last)))
                    }
                }
                while let Some(thread_last) = self.thread_iter.next(conds,pos,em)? {
                    let thread_pos = conds.len();
                    let mut frame_iter = Self::get_frame_iter(self.program,
                                                              self.thread_id.clone(),
                                                              self.thread_last,
                                                              self.frame_id.clone(),
                                                              self.frame_index.clone(),
                                                              self.exprs,em)?;
                    while let Some(frame_last) = frame_iter.next(conds,thread_pos,em)? {
                        let frame_pos = conds.len();
                        let mut instr_iter = Self::get_instr_iter(self.program,
                                                                  self.thread_id.clone(),
                                                                  thread_last,
                                                                  self.frame_id.clone(),
                                                                  frame_last,
                                                                  self.instr_id.clone(),
                                                                  self.instr_index.clone(),
                                                                  self.exprs,em)?;
                        if let Some(instr_last) = instr_iter.next(conds,frame_pos,em)? {
                            self.thread_last = thread_last;
                            self.thread_pos = thread_pos;
                            self.frame_iter = frame_iter;
                            self.frame_last = frame_last;
                            self.frame_pos = frame_pos;
                            self.instr_iter = instr_iter;
                            return Ok(Some(self.mk_view(instr_last)))
                        }
                    }
                }
                Ok(None)
            }
        }
    }
}

impl<'a,V : Bytes+FromConst<'a>+Pointer<'a>+Debug> MemLookup<'a,V> {
    pub fn load<'b,Em : Embed>(
        &self,
        dl: &'a DataLayout,
        off: &'b Offset,
        off_inp: Transf<Em>,
        len: usize,
        prog: &'b Program<'a,V>,
        prog_inp: Transf<Em>,
        em: &mut Em)
        -> Result<(OptRef<'b,V>,Transf<Em>),Em::Error> {
        match self {
            &MemLookup::Slice(ref v) => {
                let (sl,sl_inp) = v.get_with_inp(prog,prog_inp);
                match MemSlice::read(OptRef::Ref(sl),sl_inp,
                                     OptRef::Ref(off),off_inp,
                                     len,em)? {
                    None => panic!("Reading {} bytes from {:?} with offset {:?} failed.",len,sl,off),
                    Some(res) => Ok(res)
                }
            },
            &MemLookup::AuxArray => {
                let &(Data((mult,stat)),ref dyn) = off;
                match dyn {
                    &Some(_) => panic!("Dynamic index into arguments"),
                    &None => {
                        let (ptr_sz,_,_) = dl.pointer_alignment(0);
                        let ptr_byte_width = ptr_sz/8;
                        let index = mult/(ptr_byte_width as usize);
                        let cond_true = Transformation::const_bool(true,em)?;
                        let ptr_trg = PointerTrg::Aux(index);
                        let ptr_base = (ptr_trg,(Data((ptr_byte_width as usize,0)),None));
                        let (ch0,ch0_inp) = choice_empty();
                        let (ch1,ch1_inp) = choice_insert(OptRef::Owned(ch0),
                                                          ch0_inp,
                                                          cond_true,
                                                          OptRef::Owned(ptr_base),
                                                          Transformation::id(0))?;
                        Ok(V::from_pointer(ptr_byte_width as usize,ch1,ch1_inp))
                    }
                }
            },
            &MemLookup::Aux(n) => {
                //let bytes = &prog.aux[n];
                unimplemented!()
            },
            _ => unimplemented!()
        }
    }
    pub fn store<Em : Embed>(
        &self,
        off: &Offset,
        off_inp: Transf<Em>,
        val: &V,
        val_inp: Transf<Em>,
        prog: &mut Program<'a,V>,
        upd: &mut Updates<Em>,
        orig: Transf<Em>,
        em: &mut Em) -> Result<(),Em::Error> {
        match self {
            &MemLookup::Slice(ref v) => {
                let (coff,sl) = v.get_el_mut_ext(prog);
                let sl_sz = sl.num_elem();
                let sl_inp = read_updates(coff,sl.num_elem(),upd,orig);
                let ninp = sl.write(sl_inp,OptRef::Ref(off),off_inp,
                                    OptRef::Ref(val),val_inp,em)?.unwrap();
                insert_updates(upd,coff,sl_sz,ninp);
                Ok(())
            },
            _ => unimplemented!()
        }
    }
}

impl<'a,'b,V : Bytes+FromConst<'a>,Em : DeriveValues> MemLookups<'a,'b,V,Em> {
    pub fn new(trg: &PointerTrg<'a>,
               trg_inp: Transf<Em>,
               prog: &'b Program<'a,V>,
               exprs: &'b [Em::Expr],
               em: &mut Em)
               -> Result<Self,Em::Error> {
        match trg {
            &PointerTrg::Global(name)
                => Ok(MemLookups::Global(Some(name),PhantomData)),
            &PointerTrg::Heap(instr,bw) => {
                let (_,pool) = prog.heap.access(&instr);
                let it = access_dyn(pool,trg_inp,exprs,em)?;
                Ok(MemLookups::Heap(instr,it))
            },
            &PointerTrg::Stack(thr,thr_bw,
                               ref fr,fr_bw,
                               instr,instr_bw) => {
                let (_,thrs) = prog.threads.access(&thr);
                let thr_idx   = Transformation::view(0,1,trg_inp.clone());
                let fr_idx    = Transformation::view(1,1,trg_inp.clone());
                let instr_idx = Transformation::view(2,1,trg_inp);
                Ok(MemLookups::StackStart(prog,thr,thr_idx,fr.clone(),fr_idx,instr,instr_idx,exprs))
            },
            &PointerTrg::Aux(n) => Ok(MemLookups::Aux(n)),
            &PointerTrg::AuxArray => Ok(MemLookups::AuxArray),
            _ => panic!("MemLookups for {:?}",trg)
        }
    }
}

impl<'a,'b,Em : DeriveValues,V : Bytes+FromConst<'a>+Debug
     > CondIterator<Em> for MemLookups<'a,'b,V,Em> {
    type Item = MemLookup<'a,V>;
    fn next(&mut self,conds: &mut Vec<Transf<Em>>,pos: usize,em: &mut Em)
            -> Result<Option<Self::Item>, Em::Error> {
        let (nself,ret) = match self {
            &mut MemLookups::Global(ref mut name,_) => match name.take() {
                None => return Ok(None),
                Some(rname) => {
                    let view = GlobalsView::new()
                        .then(AssocView::new(rname));
                    return Ok(Some(MemLookup::Slice(PointerView::Global(view))))
                }
            },
            &mut MemLookups::Heap(instr,ref mut it)
                => match it.next(conds,pos,em)? {
                    None => return Ok(None),
                    Some(idx) => {
                        let view = HeapView::new()
                            .then(AssocView::new(instr)
                                  .then(VecView::new(idx)));
                        let pview = PointerView::Heap(view);
                        return Ok(Some(MemLookup::Slice(pview)))
                    }
                },
            &mut MemLookups::StackStart(prog,ref thr,ref thr_idx,
                                        ref fr,ref fr_idx,
                                        ref instr,ref instr_idx,exprs) => {
                match StackLookups::new(prog,thr.clone(),thr_idx.clone(),
                                        fr.clone(),fr_idx.clone(),
                                        instr.clone(),instr_idx.clone(),
                                        exprs,conds,pos,em)? {
                    None => {
                        println!("Zero entries");
                        return Ok(None)
                    },
                    Some(mut lookups) => match lookups.next(conds,pos,em)? {
                        None => return Ok(None),
                        Some(pview) => (MemLookups::Stack(lookups),
                                        Some(MemLookup::Slice(pview)))
                    }
                }
            },
            &mut MemLookups::Stack(ref mut it) => match it.next(conds,pos,em)? {
                None => return Ok(None),
                Some(pview) => return Ok(Some(MemLookup::Slice(pview)))
            },
            &mut MemLookups::Aux(n) => (MemLookups::End,
                                        Some(MemLookup::Aux(n))),
            &mut MemLookups::AuxArray => (MemLookups::End,
                                          Some(MemLookup::AuxArray)),
            &mut MemLookups::End => return Ok(None)
        };
        *self = nself;
        Ok(ret)
    }
}
*/
