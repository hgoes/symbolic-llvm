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
use super::pointer::{Pointer,PointerTrg,Offset};
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

#[derive(Clone,PartialEq,Eq,Debug)]
pub struct ThreadsPath;

#[derive(Clone,PartialEq,Eq,Debug)]
pub struct GlobalsPath;

#[derive(Clone,PartialEq,Eq,Debug)]
pub struct HeapPath;

#[derive(Clone,PartialEq,Eq,Debug)]
pub struct AuxPath;

#[derive(Clone,PartialEq,Eq,Debug)]
pub struct StepPath;

#[derive(Clone,PartialEq,Eq,Debug)]
pub struct NondetPath;

impl<'a,V> Program<'a,V> {
    pub fn threads() -> ThreadsPath {
        ThreadsPath
    }
    pub fn globals() -> GlobalsPath {
        GlobalsPath
    }
    pub fn heap() -> HeapPath {
        HeapPath
    }
    pub fn aux() -> AuxPath {
        AuxPath
    }
}

impl<'a,V: Bytes<'a>+FromConst<'a>> Program<'a,V> {
    pub fn new<Em: Embed>(inp: &mut Vec<Em::Expr>,em: &mut Em) -> Result<Self,Em::Error> {
        Ok(Program { threads: Assoc::empty(inp,em)?,
                     global: Assoc::empty(inp,em)?,
                     heap: Assoc::empty(inp,em)?,
                     aux: Choice::empty(inp,em)? })
    }
    pub fn construct<Em,FThr,FGlob,FHeap,FAux>(
        thr: FThr,
        glob: FGlob,
        hp: FHeap,
        aux: FAux,
        res: &mut Vec<Em::Expr>,
        em: &mut Em
    ) -> Result<Program<'a,V>,Em::Error>
        where Em: Embed,
              FThr: FnOnce(&mut Vec<Em::Expr>,&mut Em)
                           -> Result<Threads<'a,V>,Em::Error>,
              FGlob: FnOnce(&mut Vec<Em::Expr>,&mut Em)
                            -> Result<Globals<'a,V>,Em::Error>,
              FHeap: FnOnce(&mut Vec<Em::Expr>,&mut Em)
                            -> Result<Heap<'a,V>,Em::Error>,
              FAux: FnOnce(&mut Vec<Em::Expr>,&mut Em)
                           -> Result<Aux,Em::Error> {
        let threads = thr(res,em)?;
        let globals = glob(res,em)?;
        let heap    = hp(res,em)?;
        let raux    = aux(res,em)?;
        Ok(Program { threads: threads,
                     global: globals,
                     heap: heap,
                     aux: raux })
    }
    pub fn is_single_threaded(&self) -> bool {
        match self.threads.is_single() {
            None => false,
            Some(&(_,_,ref thrs)) => thrs.len()==1
        }
    }
}

impl<'a,V: 'a+HasSorts> ProgramInput<'a,V> {
    pub fn new_sig() -> Self {
        ProgramInput {
            step: Choice::empty_sig(),
            nondet: Assoc::empty_sig()
        }
    }
    pub fn step() -> StepPath {
        StepPath
    }
    pub fn nondet() -> NondetPath {
        NondetPath
    }
    pub fn thread_activation<From,P,Em>(
        thread_id: &ThreadId<'a>,
        path: P,
        from: &'a From,
        arr:  &'a [Em::Expr],
        em:   &mut Em
    ) -> Result<Option<(Em::Expr,Em::Expr)>,Em::Error>
        where P: 'a+Path<'a,Em,From,To=Self>,
              Em: Embed {
        match Choice::elements(path.then(Self::step()),from)
            .find(|p| (p.get(from).0).0==*thread_id) {
                None => Ok(None),
                Some(p) => {
                    let cond = Choice::is_selected(&p,from,arr,em)?;
                    let idx = p.read(from,0,arr,em)?;
                    Ok(Some((cond,idx)))
                }
            }
    }
    pub fn add_thread(&mut self,thread_id: ThreadId<'a>) -> () {
        self.step.add((Data(thread_id),SingletonBitVec(STEP_BW)));
    }
}

impl<'a,V: 'a> SimplePathEl<'a,Program<'a,V>> for ThreadsPath {
    type To = Threads<'a,V>;
    fn get<'b>(&self,obj: &'b Program<'a,V>)
               -> &'b Self::To where 'a: 'b {
        &obj.threads
    }
    fn get_mut<'c>(&self,from: &'c mut Program<'a,V>)
                   -> &'c mut Self::To where 'a: 'c {
        &mut from.threads
    }
}

impl<'a,V: 'a,Em: Embed> PathEl<'a,Em,Program<'a,V>> for ThreadsPath {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Program<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        prev.read(prev_from,pos,arr,em)
    }
    fn read_slice<'c,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Program<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        len: usize,
        arr: &'c [Em::Expr])
        -> Option<&'c [Em::Expr]> {
        prev.read_slice(prev_from,pos,len,arr)
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Program<'a,V>>>(
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
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Program<'a,V>>>(
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

impl<'a,V: 'a+HasSorts> SimplePathEl<'a,Program<'a,V>> for GlobalsPath {
    type To = Globals<'a,V>;
    fn get<'b>(&self,obj: &'b Program<'a,V>)
               -> &'b Self::To where 'a: 'b {
        &obj.global
    }
    fn get_mut<'c>(&self,from: &'c mut Program<'a,V>)
                   -> &'c mut Self::To where 'a: 'c {
        &mut from.global
    }
}

impl<'a,V: 'a+HasSorts,Em: Embed> PathEl<'a,Em,Program<'a,V>> for GlobalsPath {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Program<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        let off = prev.get(prev_from).threads.num_elem();
        prev.read(prev_from,pos+off,arr,em)
    }
    fn read_slice<'c,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Program<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        len: usize,
        arr: &'c [Em::Expr])
        -> Option<&'c [Em::Expr]> {
        let off = prev.get(prev_from).threads.num_elem();
        prev.read_slice(prev_from,pos+off,len,arr)
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Program<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        e: Em::Expr,
        arr: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        let off = prev.get(prev_from).threads.num_elem();
        prev.write(prev_from,pos+off,e,arr,em)
    }
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Program<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &mut PrevFrom,
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

impl<'a,V: 'a+HasSorts> SimplePathEl<'a,Program<'a,V>> for HeapPath {
    type To = Heap<'a,V>;
    fn get<'b>(&self,obj: &'b Program<'a,V>)
               -> &'b Self::To where 'a: 'b {
        &obj.heap
    }
    fn get_mut<'c>(&self,from: &'c mut Program<'a,V>)
                   -> &'c mut Self::To where 'a: 'c {
        &mut from.heap
    }
}

impl<'a,V: 'a+HasSorts,Em: Embed> PathEl<'a,Em,Program<'a,V>> for HeapPath {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Program<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
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
    fn read_slice<'c,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Program<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
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
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Program<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
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
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Program<'a,V>>>(
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
            let prog = prev.get(prev_from);
            prog.threads.num_elem() +
                prog.global.num_elem()
        };
        prev.write_slice(prev_from,pos+off,old_len,src,trg,em)
    }
}

impl<'a,V: HasSorts> SimplePathEl<'a,Program<'a,V>> for AuxPath {
    type To = Aux;
    fn get<'b>(&self,obj: &'b Program<'a,V>)
               -> &'b Self::To where 'a: 'b {
        &obj.aux
    }
    fn get_mut<'c>(&self,from: &'c mut Program<'a,V>)
                   -> &'c mut Self::To where 'a: 'c {
        &mut from.aux
    }
}

impl<'a,V: 'a+HasSorts,Em: Embed> PathEl<'a,Em,Program<'a,V>> for AuxPath {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Program<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
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
    fn read_slice<'c,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Program<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
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
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Program<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
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
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Program<'a,V>>>(
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
            let prog = prev.get(prev_from);
            prog.threads.num_elem() +
                prog.global.num_elem() +
                prog.heap.num_elem()
        };
        prev.write_slice(prev_from,pos+off,old_len,src,trg,em)
    }
}

impl<'a,V> SimplePathEl<'a,ProgramInput<'a,V>> for StepPath {
    type To = Step<'a>;
    fn get<'b>(&self,obj: &'b ProgramInput<'a,V>)
               -> &'b Self::To where 'a: 'b {
        &obj.step
    }
    fn get_mut<'c>(&self,from: &'c mut ProgramInput<'a,V>)
                   -> &'c mut Self::To where 'a: 'c {
        &mut from.step
    }
}

impl<'a,V: 'a,Em: Embed> PathEl<'a,Em,ProgramInput<'a,V>> for StepPath {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=ProgramInput<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        prev.read(prev_from,pos,arr,em)
    }
    fn read_slice<'c,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=ProgramInput<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        len: usize,
        arr: &'c [Em::Expr])
        -> Option<&'c [Em::Expr]> {
        prev.read_slice(prev_from,pos,len,arr)
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=ProgramInput<'a,V>>>(
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
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=ProgramInput<'a,V>>>(
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

impl<'a,V: 'a+HasSorts> SimplePathEl<'a,ProgramInput<'a,V>> for NondetPath {
    type To = Nondet<'a,V>;
    fn get<'b>(&self,obj: &'b ProgramInput<'a,V>)
               -> &'b Self::To where 'a: 'b {
        &obj.nondet
    }
    fn get_mut<'c>(&self,from: &'c mut ProgramInput<'a,V>)
                   -> &'c mut Self::To where 'a: 'c {
        &mut from.nondet
    }
}

impl<'a,V: 'a+HasSorts,Em: Embed> PathEl<'a,Em,ProgramInput<'a,V>> for NondetPath {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=ProgramInput<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        let off = prev.get(prev_from).step.num_elem();
        prev.read(prev_from,pos+off,arr,em)
    }
    fn read_slice<'c,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=ProgramInput<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        len: usize,
        arr: &'c [Em::Expr])
        -> Option<&'c [Em::Expr]> {
        let off = prev.get(prev_from).step.num_elem();
        prev.read_slice(prev_from,pos+off,len,arr)
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=ProgramInput<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &PrevFrom,
        pos: usize,
        e: Em::Expr,
        arr: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        let off = prev.get(prev_from).step.num_elem();
        prev.write(prev_from,pos+off,e,arr,em)
    }
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=ProgramInput<'a,V>>>(
        &self,
        prev: &Prev,
        prev_from: &mut PrevFrom,
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
}*/

#[derive(Clone)]
pub enum PointerPath<Prev> {
    Global(Then<Then<Prev,GlobalsPath>,
                AssocP>),
    Heap(Then<Then<Then<Prev,HeapPath>,
                   AssocP>,
              CompVecP>),
    Stack(Then<Then<Then<FramePath<Then<Then<Then<Prev,ThreadsPath>,
                                             AssocP>,
                                        CompVecP>>,
                         AllocationsPath>,
                    AssocP>,
               CompVecP>),
}

impl<'a,From,Prev: SimplePath<'a,From,To=Program<'a,V>>,V>
    SimplePath<'a,From> for PointerPath<Prev>
    where V: 'a+HasSorts {

    type To = MemSlice<'a,V>;

    fn get<'b>(&self,from: &'b From)
               -> &'b Self::To where 'a: 'b {
        match self {
            &PointerPath::Global(ref p) => p.get(from),
            &PointerPath::Heap(ref p) => p.get(from),
            &PointerPath::Stack(ref p) => p.get(from)
        }
    }
    fn get_mut<'b>(&self,from: &'b mut From)
                   -> &'b mut Self::To where 'a: 'b {
        match self {
            &PointerPath::Global(ref p) => p.get_mut(from),
            &PointerPath::Heap(ref p) => p.get_mut(from),
            &PointerPath::Stack(ref p) => p.get_mut(from)
        }
    }
}

impl<'a,Em: Embed,From,Prev: Path<'a,Em,From,To=Program<'a,V>>,V>
    Path<'a,Em,From> for PointerPath<Prev>
    where V: 'a+Bytes<'a>+FromConst<'a> {

    fn read(
        &self,
        from: &From,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        match self {
            &PointerPath::Global(ref p) => p.read(from,pos,arr,em),
            &PointerPath::Heap(ref p) => p.read(from,pos,arr,em),
            &PointerPath::Stack(ref p) => p.read(from,pos,arr,em)
        }
    }
    fn read_slice<'c>(
        &self,
        from: &From,
        pos: usize,
        len: usize,
        arr: &'c [Em::Expr])
        -> Option<&'c [Em::Expr]> {

        match self {
            &PointerPath::Global(ref p) => p.read_slice(from,pos,len,arr),
            &PointerPath::Heap(ref p) => p.read_slice(from,pos,len,arr),
            &PointerPath::Stack(ref p) => p.read_slice(from,pos,len,arr)
        }
    }
    fn write(
        &self,
        from: &From,
        pos: usize,
        e: Em::Expr,
        arr: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        match self {
            &PointerPath::Global(ref p) => p.write(from,pos,e,arr,em),
            &PointerPath::Heap(ref p) => p.write(from,pos,e,arr,em),
            &PointerPath::Stack(ref p) => p.write(from,pos,e,arr,em)
        }
    }
    fn write_slice(
        &self,
        from: &mut From,
        pos: usize,
        old_len: usize,
        src: &mut Vec<Em::Expr>,
        trg: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        match self {
            &PointerPath::Global(ref p)
                => p.write_slice(from,pos,old_len,src,trg,em),
            &PointerPath::Heap(ref p)
                => p.write_slice(from,pos,old_len,src,trg,em),
            &PointerPath::Stack(ref p)
                => p.write_slice(from,pos,old_len,src,trg,em)
        }
    }
}

#[derive(Clone)]
pub enum ProgramMeaning<'b,V: Semantic+Bytes<'b>+FromConst<'b>> {
    Threads(<Threads<'b,V> as Semantic>::Meaning),
    Global(<Globals<'b,V> as Semantic>::Meaning),
    Heap(<Heap<'b,V> as Semantic>::Meaning),
    Aux(<Aux as Semantic>::Meaning)
}

pub enum ProgramMeaningCtx<'b,V: Semantic+Bytes<'b>+FromConst<'b>> {
    Threads(<Threads<'b,V> as Semantic>::MeaningCtx),
    Global(<Globals<'b,V> as Semantic>::MeaningCtx),
    Heap(<Heap<'b,V> as Semantic>::MeaningCtx),
    Aux(<Aux as Semantic>::MeaningCtx)
}

impl<'b,V: Semantic+Bytes<'b>+FromConst<'b>> PartialEq for ProgramMeaning<'b,V> {
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

impl<'b,V: Semantic+Bytes<'b>+FromConst<'b>> Eq for ProgramMeaning<'b,V> {}

impl<'b,V: Semantic+Bytes<'b>+FromConst<'b>> PartialOrd for ProgramMeaning<'b,V> {
    fn partial_cmp(&self,other: &ProgramMeaning<'b,V>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<'b,V: Semantic+Bytes<'b>+FromConst<'b>> Ord for ProgramMeaning<'b,V> {
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

impl<'b,V: Semantic+Bytes<'b>+FromConst<'b>> Hash for ProgramMeaning<'b,V> {
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

impl<'b,V: Semantic+Bytes<'b>+FromConst<'b>> fmt::Debug for ProgramMeaning<'b,V> {
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


impl<'b,V: Semantic+Bytes<'b>+FromConst<'b>> ProgramMeaning<'b,V> {
    pub fn is_pc(&self) -> bool {
        match self {
            &ProgramMeaning::Threads(ref m) => m.meaning.meaning.is_pc(),
            _ => false
        }
    }
}

impl<'b,V: Semantic+Bytes<'b>+FromConst<'b>> Semantic for Program<'b,V> {
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

pub enum MemLookup {
    Slice(PointerPath<Id>),
    Aux(usize),
    AuxArray
}

pub enum MemLookups<'a,V: 'a,Em: DeriveValues>
    where Em::Expr: 'a {
    Global(Option<Then<Then<Id,
                            GlobalsPath>,
                       AssocP>>),
    Heap(DynVecAccess<Then<Then<Id,
                                HeapPath>,
                           AssocP>,
                      Em>),
    Stack(ProgramMemSliceAccess<'a,Program<'a,V>,Id,V,Em>),
    Aux(usize),
    AuxArray,
    End
}

impl<'a,Em: DeriveValues,V> MemLookups<'a,V,Em>
    where
    V: 'a+Bytes<'a>+FromConst<'a> {
    pub fn next(&mut self,conds: &mut Vec<Em::Expr>,pos: usize,from: &Program<'a,V>,from_arr: &[Em::Expr],em: &mut Em)
                -> Result<Option<MemLookup>, Em::Error> {
        match self {
            &mut MemLookups::Global(ref mut p) => match p.take() {
                None => Ok(None),
                Some(path) => Ok(Some(MemLookup::Slice(PointerPath::Global(path))))
            },
            &mut MemLookups::Heap(ref mut acc) => match acc.next(conds,pos,em)? {
                None => Ok(None),
                Some(path) => Ok(Some(MemLookup::Slice(PointerPath::Heap(path))))
            },
            &mut MemLookups::Stack(ref mut acc) => match acc.next(conds,pos,from,from_arr,em)? {
                None => Ok(None),
                Some(path) => Ok(Some(MemLookup::Slice(PointerPath::Stack(path))))
            },
            &mut MemLookups::Aux(n) => {
                *self = MemLookups::End;
                Ok(Some(MemLookup::Aux(n)))
            },
            &mut MemLookups::AuxArray => {
                *self = MemLookups::End;
                Ok(Some(MemLookup::AuxArray))
            },
            &mut MemLookups::End => Ok(None)
        }
    }
}

pub type ThreadAccess<Prev,Em: DeriveValues>
    = DynVecAccess<Then<Then<Prev,
                             ThreadsPath>,
                        AssocP>,Em>;

pub struct ProgramFrameAccess<'a,From: 'a,Prev,V: 'a,Em>
    where
    Em: DeriveValues {
    thread_it: ThreadAccess<Prev,Em>,
    frame_id:  FrameId<'a>,
    frame_it:  Option<(FrameAccess<'a,From,
                                   Then<Then<Then<Prev,
                                                  ThreadsPath>,
                                             AssocP>,
                                        CompVecP>,
                                   V,Em>,usize)>
}

impl<'a,From,Prev,V,Em> ProgramFrameAccess<'a,From,Prev,V,Em>
    where
    Prev: Path<'a,Em,From,To=Program<'a,V>>,
    V: 'a+Clone+HasSorts,
    Em: DeriveValues {
    pub fn next(&mut self,
                conds: &mut Vec<Em::Expr>,
                pos: usize,
                from: &From,
                from_arr: &[Em::Expr],
                em: &mut Em) -> Result<Option<FramePath<Then<Then<Then<Prev,
                                                                       ThreadsPath>,
                                                                  AssocP>,
                                                             CompVecP>>>,Em::Error> {
        loop {
            if let Some((ref mut acc,npos)) = self.frame_it {
                if let Some(path) = acc.next(conds,npos,em)? {
                    return Ok(Some(path))
                }
            }
            match self.thread_it.next(conds,pos,em)? {
                None => return Ok(None),
                Some(path) => {
                    let npos = conds.len();
                    let acc = FrameAccess::new(path,
                                               from,
                                               from_arr,
                                               &self.frame_id,
                                               em)?;
                    self.frame_it = Some((acc,npos));
                }
            }
        }
    }
}

pub struct ProgramMemSliceAccess<'a,From: 'a,Prev,V: 'a,Em>
    where
    Em: DeriveValues {
    frame_iter: ProgramFrameAccess<'a,From,Prev,V,Em>,
    alloc_id: InstructionRef<'a>,
    alloc_index: Em::Expr,
    alloc_iter: Option<(DynVecAccess<Then<Then<FramePath<Then<Then<Then<Prev,
                                                                        ThreadsPath>,
                                                                   AssocP>,
                                                              CompVecP>>,
                                               AllocationsPath>,
                                          AssocP>,
                                     Em>,usize)>,
    phantom: PhantomData<V>
}

impl<'a,From,Prev,V,Em> ProgramMemSliceAccess<'a,From,Prev,V,Em>
    where
    Em: DeriveValues,
    V: 'a+Bytes<'a>+FromConst<'a>+Clone,
    Em::Expr: 'a {
    pub fn new(
        path: Prev,
        from: &From,
        from_arr: &[Em::Expr],
        thread_id: ThreadId<'a>,
        thread_index: Em::Expr,
        frame_id: FrameId<'a>,
        frame_index: Em::Expr,
        alloc_id: InstructionRef<'a>,
        alloc_index: Em::Expr,
        em: &mut Em
    ) -> Result<Self,Em::Error>
        where Prev: Path<'a,Em,From,To=Program<'a,V>> {
        let thr_path = Assoc::lookup(then(path,ThreadsPath),
                                     from,
                                     &thread_id).expect("Thread not found");
        let thr_it = CompVec::access_dyn(thr_path,from,thread_index,em)?;
        let fr_acc = ProgramFrameAccess {
            thread_it: thr_it,
            frame_id: frame_id,
            frame_it: None
        };
        let alloc_acc = ProgramMemSliceAccess {
            frame_iter: fr_acc,
            alloc_id: alloc_id,
            alloc_index: alloc_index,
            alloc_iter: None,
            phantom: PhantomData
        };
        Ok(alloc_acc)
    }
}

impl<'a,From,Prev,V,Em> ProgramMemSliceAccess<'a,From,Prev,V,Em>
    where
    Prev: Path<'a,Em,From,To=Program<'a,V>>,
    V: 'a+Clone+HasSorts,
    Em: DeriveValues,
    Em::Expr: 'a {
    pub fn next(&mut self,
                conds: &mut Vec<Em::Expr>,
                pos: usize,
                from: &From,
                from_arr: &[Em::Expr],
                em: &mut Em) -> Result<Option<Then<Then<Then<FramePath<Then<Then<Then<Prev,
                                                                                      ThreadsPath>,
                                                                                 AssocP>,
                                                                            CompVecP>>,
                                                             AllocationsPath>,
                                                        AssocP>,
                                                   CompVecP>>,Em::Error> {
        loop {
            if let Some((ref mut acc,cpos)) = self.alloc_iter {
                if let Some(path) = CondIterator::next(acc,conds,cpos,em)? {
                    return Ok(Some(path))
                }
            }
            match self.frame_iter.next(conds,pos,from,from_arr,em)? {
                None => return Ok(None),
                Some(fr) => {
                    let npos = conds.len();
                    let niter = CompVec::access_dyn(
                        Assoc::lookup(then(fr,AllocationsPath),
                                      from,
                                      &self.alloc_id)
                            .expect("Allocation not found"),
                        from,
                        self.alloc_index.clone(),
                        em)?;
                    self.alloc_iter = Some((niter,npos));
                }
            }
        }
    }
}


/*
impl<'a : 'b,'b,V: 'a+Bytes+FromConst<'a>+Debug,Em: DeriveValues> StackLookups<'a,'b,V,Em>
    where Em::Expr : 'b {
    fn new(program: &'b Program<'a,V>,
           thread_id: ThreadId<'a>,
           thread_index: Em::Expr,
           frame_id: FrameId<'a>,
           frame_index: Em::Expr,
           instr_id: InstructionRef<'a>,
           instr_index: Em::Expr,
           conds: &mut Vec<Em::Expr>,
           pos: usize,
           em: &mut Em) -> Result<Option<Self>,Em::Error> {
        let path = Assoc::lookup(Id::new()
                                 .then(Program::threads()),
                                 &program,
                                 &thread_id).expect("Cannot find thread");
        /*{ // Debugging
            let frame_idx_ = frame_index.get(exprs,0,em)?;
            println!("ACCESS DYN {:?}, {:?}",pool,match em.derive_values(&frame_idx_)? {
                None => vec![],
                Some(it) => it.collect::<Vec<_>>()
            });
        }*/
        let mut thread_iter = CompVec::access_dyn(&path,&program,
                                                  thread_index,em)?;
        while let Some(thread_last) = thread_iter.next(conds,pos,em)? {
            let thread_pos = conds.len();
            let mut frame_iter = Self::get_frame_iter(thread_last,
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
    fn get_frame_iter<P: SimplePath<'a,To=Thread<'a,V>>>(
        path: P,
        from: &P::From,
        frame_id: FrameId<'a>,
        frame_index: Em::Expr,
        em: &mut Em) -> Result<IndexedIter<Em>,Em::Error> {
        match frame_id {
            FrameId::Call(cid) => {
                let npath = Assoc::lookup(path
                                          .then(Thread::call_stack()),
                                          from,cid)
                    .expect("Cannot find call frame");
                CompVec::access_dyn_iter(&npath,from,
                                         frame_index,em)
            },
            FrameId::Stack(i) => {
                let npath = Assoc::lookup(path
                                          .then(Thread::stack()),
                                          from,i)
                    .expect("Cannot find stack frame");
                CompVec::access_dyn_iter(&npath,from,
                                         frame_index,em)
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
}*/

impl MemLookup {
    pub fn load<'a,V: Bytes<'a>+FromConst<'a>+Pointer<'a>+Debug,
                Em: Embed,FromOff,POff: Path<'a,Em,FromOff,To=Offset>>(
        &self,
        dl: &DataLayout,
        off: &POff,
        off_from: &FromOff,
        off_inp: &[Em::Expr],
        len: usize,
        prog: &Program<'a,V>,
        prog_inp: &[Em::Expr],
        res: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<V,Em::Error> {
        match self {
            &MemLookup::Slice(ref v) => {
                match MemSlice::read(v,prog,prog_inp,
                                     off,off_from,off_inp,
                                     len,res,em)? {
                    None => panic!("Reading {} bytes failed.",len),
                    Some(res) => Ok(res)
                }
            },
            &MemLookup::AuxArray => {
                let &(Data((mult,stat)),ref dyn) = off.get(off_from);
                match dyn {
                    &Some(_) => panic!("Dynamic index into arguments"),
                    &None => {
                        let (ptr_sz,_,_) = dl.pointer_alignment(0);
                        let ptr_byte_width = ptr_sz/8;
                        let index = mult/(ptr_byte_width as usize);
                        let mut ptr_inp = Vec::new();
                        let ptr = Choice::singleton(|res,em| {
                            let ptr_trg = PointerTrg::Aux(index);
                            let ptr_base = (ptr_trg,(Data((ptr_byte_width as usize,0)),None));
                            Ok(ptr_base)
                        },&mut ptr_inp,em)?;
                        V::from_pointer(ptr_byte_width as usize,
                                        &Id::new(),&ptr,&ptr_inp[..],res,em)
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
    pub fn store<'a,Em: Embed,FromOff,POff,V>(
        &self,
        off: &POff,
        off_from: &FromOff,
        off_inp: &[Em::Expr],
        val: V,
        val_inp: &mut Vec<Em::Expr>,
        prog: &mut Program<'a,V>,
        prog_inp: &mut Vec<Em::Expr>,
        cond: Option<Em::Expr>,
        em: &mut Em) -> Result<(),Em::Error>
        where POff: Path<'a,Em,FromOff,To=Offset>,
              V: 'a+Bytes<'a>+FromConst<'a> {
        match self {
            &MemLookup::Slice(ref v) => {
                MemSlice::write(v.clone(),prog,prog_inp,
                                off,off_from,off_inp,
                                val,val_inp,cond,em)
            },
            _ => unimplemented!()
        }
    }
}

impl<'a,V: Bytes<'a>+FromConst<'a>,Em: DeriveValues> MemLookups<'a,V,Em> {
    pub fn new<From,P>(trg: &P,
                       from: &From,
                       inp: &[Em::Expr],
                       prog: &Program<'a,V>,
                       prog_inp: &[Em::Expr],
                       em: &mut Em)
                       -> Result<Self,Em::Error>
        where P: Path<'a,Em,From,To=PointerTrg<'a>> {
        match trg.get(from) {
            &PointerTrg::Global(name)
                => match Assoc::lookup(then(Id,GlobalsPath),
                                       prog,&name) {
                    None => panic!("Global {} not found",name),
                    Some(path) => Ok(MemLookups::Global(Some(path)))
                },
            &PointerTrg::Heap(instr,bw) => {
                let idx = trg.read(from,0,inp,em)?;
                match Assoc::lookup(then(Id,HeapPath),
                                    prog,&instr) {
                    None => panic!("Heap for {:?} not found",instr),
                    Some(path) => {
                        let acc = CompVec::access_dyn(path,prog,idx,em)?;
                        Ok(MemLookups::Heap(acc))
                    }
                }
            },
            &PointerTrg::Stack(thr,thr_bw,
                               ref fr,fr_bw,
                               instr,instr_bw) => {
                let thr_idx   = trg.read(from,0,inp,em)?;
                let fr_idx    = trg.read(from,1,inp,em)?;
                let instr_idx = trg.read(from,2,inp,em)?;
                let acc = ProgramMemSliceAccess::new(
                    Id::new(),prog,prog_inp,
                    thr,thr_idx,
                    fr.clone(),fr_idx,
                    instr,instr_idx,em)?;
                Ok(MemLookups::Stack(acc))
            },
            &PointerTrg::Aux(n) => Ok(MemLookups::Aux(n)),
            &PointerTrg::AuxArray => Ok(MemLookups::AuxArray),
            l => panic!("MemLookups for {:?}",l)
        }
    }
}

/*impl<'a,'b,Em : DeriveValues,V : Bytes+FromConst<'a>+Debug
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
