pub mod mem;
pub mod frame;
pub mod thread;
pub mod program;
//pub mod error;
pub mod pointer;
pub mod library;

use smtrs::composite::*;
use smtrs::composite::singleton::*;
use smtrs::composite::vec::*;
use smtrs::composite::map::*;
use smtrs::composite::stack::*;
use smtrs::composite::choice::*;
use smtrs::composite::tuple::*;
use smtrs::embed::{Embed,DeriveConst,DeriveValues};
use smtrs::types::{Sort,SortKind,Value};
use num_bigint::BigUint;
use num_traits::cast::ToPrimitive;
use std::ops::Shl;
use std::fmt::Debug;
use std::collections::HashMap;
use self::mem::{Bytes,FromConst,MemSlice,MemObj};
use self::frame::*;
use self::thread::*;
use self::program::*;
use self::pointer::*;
use self::library::Library;
use llvm_ir;
use llvm_ir::Module;
use llvm_ir::datalayout::{DataLayout};
use llvm_ir::types::{Type};
use std::iter::{Once,once};
use std::cmp::Ordering;
use std::hash::{Hash,Hasher};
use std::fmt;
use std::marker::PhantomData;
use std::mem::swap;

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash,Copy,Clone,Debug)]
pub struct InstructionRef<'a> {
    pub function: &'a String,
    pub basic_block: &'a String,
    pub instruction: usize
}

pub enum TrErr<'a,V: Bytes<'a>+Clone,Err> {
    EmErr(Err),
    InputNeeded(ProgramInput<'a,V>)
}

impl<'a,V: Bytes<'a>+Clone,Err> From<Err> for TrErr<'a,V,Err> {
    fn from(err:Err) -> Self {
        TrErr::EmErr(err)
    }
}

impl<'a> InstructionRef<'a> {
    pub fn entry(fun: &'a llvm_ir::Function) -> Self {
        InstructionRef {
            function: &fun.name,
            basic_block: &fun.body.as_ref().expect("Function has no body")[0].name,
            instruction: 0
        }
    }
    pub fn resolve(&self,m: &'a llvm_ir::Module) -> &'a llvm_ir::Instruction {
        match m.functions.get(self.function) {
            None => panic!("When resolving: {}.{}.{}: Function not found.",
                           self.function,self.basic_block,self.instruction),
            Some(fun) => self.resolve_fun(fun)
        }
    }
    pub fn resolve_fun(&self,fun: &'a llvm_ir::Function) -> &'a llvm_ir::Instruction {
        let instrs= &fun.body.as_ref().expect("Function has no body")
            .iter()
            .find(|bb| bb.name == *self.basic_block).expect("Cannot find basic block")
            .instrs;
        if instrs.len() <= self.instruction {
            panic!("When resolving: {}.{}.{}: Too few instructions in block",
                   fun.name,self.basic_block,self.instruction)
        } else {
            &instrs[self.instruction]
        }
    }
    pub fn next(&self) -> Self {
        InstructionRef { function: self.function,
                         basic_block: self.basic_block,
                         instruction: self.instruction + 1 }
    }
}

const INDEX_WIDTH: usize = 32;

pub fn translate_init<'a,FArgs,FAux,V,Em>(
    module: &'a Module,
    entry_fun: &'a String,
    args: FArgs,
    aux: FAux,
    res: &mut Vec<Em::Expr>,
    em: &mut Em)
    -> Result<Program<'a,V>,Em::Error>
    where FArgs: FnOnce(&mut Vec<Em::Expr>,&mut Em)
                        -> Result<CompVec<V>,Em::Error>,
          FAux: FnOnce(&mut Vec<Em::Expr>,&mut Em)
                       -> Result<Aux,Em::Error>,
          V: 'a+Bytes<'a>+FromConst<'a>+Clone,
          Em: Embed {

    let main_fun = module.functions.get(entry_fun).expect("Entry function not found in module");
    let main_blk = match main_fun.body {
        None => panic!("Entry function has no body"),
        Some(ref bbs) => if bbs.len()==0 {
            panic!("Entry function has no basic blocks")
        } else {
            &bbs[0].name
        }
    };

    Program::construct(
        |res,em| { // Threads
            Assoc::singleton((None,entry_fun),|res,em| {
                CompVec::singleton(
                    |res,em| {
                        Thread::construct(
                            |res,em| { // Call stack
                                Assoc::singleton((None,entry_fun),|res,em| {
                                    BitVecVectorStack::singleton(
                                        INDEX_WIDTH,
                                        |res,em| tuple(|res,em| {
                                            CallFrame::construct(
                                                Assoc::empty,
                                                args,
                                                |res,em| {
                                                    Choice::singleton(|_,_| {
                                                        Ok(Data(InstructionRef { function: entry_fun,
                                                                                 basic_block: main_blk,
                                                                                 instruction: 0 }))
                                                    },res,em)
                                                },
                                                Choice::empty,
                                                res,em)
                                        },|res,em| {
                                            Frame::construct(
                                                |res,em| {
                                                    Choice::singleton(|_,_| {
                                                        Ok(Data(None))
                                                    },res,em)
                                                },
                                                Assoc::empty,
                                                res,em)
                                        },res,em),
                                        res,em)
                                },res,em)
                            },
                            Assoc::empty, // Stack
                            |res,em| { // Stack top
                                Choice::singleton(
                                    |_,_| {
                                        Ok(Data(Some(ContextId::Call((None,entry_fun)))))
                                    },res,em)
                            },
                            |_,_| { Ok(None) }, // Return value
                            res,em)
                    },res,em)
            },res,em)
        },
        |res,em| { // Globals
            Assoc::construct(
                module.globals.iter(),
                false,
                |(name,glob),res,em| {
                    let el = match glob.initialization {
                        None => {
                            let sz = module.datalayout.type_size_in_bits(&glob.types,&module.types);
                            let vec = CompVec::singleton(
                                |_,_| Ok(MemObj::FreshObj(sz as usize)),
                                res,em)?;
                            MemSlice(vec)
                        },
                        Some(ref init) => translate_global(&module.datalayout,
                                                           init,
                                                           &glob.types,
                                                           &module.types,
                                                           res,em)?
                    };
                    Ok((name,el))
                },res,em)
        },
        Assoc::empty, // Heap
        aux,
        res,em)
}

/*fn filter_ctx_id<'a,V>(cf_id: &CallId<'a>,el: (ThreadView<'a,V>,&Data<Option<ContextId<'a>>>))
                       -> Option<(ThreadView<'a,V>,ContextId<'a>)> {
    match (el.1).0 {
        None => None,
        Some(ContextId::Call(cid)) => if cid==*cf_id { Some((el.0,ContextId::Call(cid))) } else { None },
        Some(ContextId::Stack(cid,instr)) => if cid==*cf_id { Some((el.0,ContextId::Stack(cid,instr))) } else { None }
    }
}

fn is_builtin(name: &String) -> bool {
    if name.starts_with("llvm.dbg") {
        return true;
    }
    false
}

fn conds_true<Em : DeriveConst>(conds: &Vec<Transf<Em>>,exprs: &[Em::Expr],em: &mut Em) -> Result<bool,Em::Error> {
    for el in conds.iter() {
        let e = el.get(exprs,0,em)?;
        match em.derive_const(&e)? {
            Some(Value::Bool(true)) => continue,
            _ => return Ok(false)
        }
    }
    Ok(true)
}*/

fn update_activation<'a,Em : Embed,From,P: Path<'a,Em,From,To=Activation<'a>>>(
    path: &P,
    from: &mut From,
    cont: &mut Vec<Em::Expr>,
    conds: &Vec<Em::Expr>,
    instr_id: InstructionRef<'a>,
    em: &mut Em
) -> Result<(),Em::Error> {

    let rcond = if conds.len()==0 {
        let mut ch0_inp = Vec::new();
        let ch0 = Choice::empty(&mut ch0_inp,em)?;
        path.set(from,cont,ch0,&mut ch0_inp,em)?;
        em.const_bool(true)?
    } else {
        em.and(conds.clone())?
    };
    let mut inp = Vec::new();
    Choice::set_chosen(path,from,cont,
                       Data(instr_id),&mut inp,rcond,em)
}

pub trait TranslationCfg<Em: Embed> {
    fn change_thread_activation(
        &mut self,
        _:&mut Vec<Em::Expr>,_:usize,_:&mut Em)
        -> Result<(),Em::Error> {
        Ok(())
    }
    fn change_context_activation(
        &mut self,
        _:&mut Vec<Em::Expr>,_:usize,_:&mut Em)
        -> Result<(),Em::Error> {
        Ok(())
    }
    fn change_call_frame_activation(
        &mut self,
        _:&mut Vec<Em::Expr>,_:usize,_:&mut Em)
        -> Result<(),Em::Error> {
        Ok(())
    }
    fn change_instr_activation(
        &mut self,
        _:&mut Vec<Em::Expr>,_:usize,_:&mut Em)
        -> Result<(),Em::Error> {
        Ok(())
    }
    fn change_instr_not_blocking(
        &mut self,
        _:&mut Vec<Em::Expr>,_:usize,_:&mut Em)
        -> Result<(),Em::Error> {
        Ok(())
    }
}

pub struct DefaultCfg {}

impl<Em : Embed> TranslationCfg<Em> for DefaultCfg {}
/*
fn eval_phi<'a,'b,ValsView,V,Em>(m: &'b Module,
                                 fun: &'b String,
                                 src: &'b String,
                                 trg: &'b String,
                                 vals_view: &ValsView,
                                 call_frame: &CallFrame<'b,V>,
                                 call_frame_inp: Transf<Em>,
                                 conds: &Vec<Transf<Em>>,
                                 nprog: &mut Program<'b,V>,
                                 updates: &mut Updates<Em>,
                                 prog_inp: Transf<Em>,
                                 exprs: &[Em::Expr],
                                 em: &mut Em) -> Result<(),Em::Error>
    where ValsView: ViewMut<Viewed=Program<'b,V>,Element=Assoc<&'b String,V>>+Clone,
          V: 'b+Bytes+FromConst<'b>+IntValue+Vector+Pointer<'b>+FromMD<'b>+Debug,
          Em: DeriveValues {
    let trg_blk = match m.functions.get(fun) {
        None => panic!("Function not found"),
        Some(ref fun) => match fun.body {
            None => panic!("Function has no body"),
            Some(ref bdy) => match bdy.iter().find(|blk| blk.name==*trg) {
                None => panic!("Basic block not found"),
                Some(blk) => blk
            }
        }
    };
    for i in trg_blk.instrs.iter() {
        match i.content {
            llvm_ir::InstructionC::Phi(ref name,ref tp,ref srcs) => {
                let value_view = vals_view.clone().then(AssocView::new(name));
                match srcs.iter().find(|&&(_,ref csrc)| *csrc==*src) {
                    None => panic!("Block not found in phis"),
                    Some(&(ref val,_)) => {
                        let (rval,rval_inp) = translate_value(&m.datalayout,
                                                              &val,&tp,&m.types,
                                                              call_frame,
                                                              call_frame_inp.clone(),
                                                              exprs,em)?;
                        value_view.insert_cond(nprog,
                                               rval,rval_inp,
                                               conds,updates,prog_inp.clone(),em)?;
                    }
                }
            },
            _ => break
        }
    }
    Ok(())
}*/

pub fn translate_instr<'b,V,Cfg,Lib,Em>(
    m: &'b Module,
    cfg: &mut Cfg,
    lib: &Lib,
    thread_id: ThreadId<'b>,
    cf_id: CallId<'b>,
    instr_id: InstructionRef<'b>,
    instr: &'b llvm_ir::Instruction,
    prog: &mut Program<'b,V>,
    inp: &ProgramInput<'b,V>,
    prog_inp: &mut Vec<Em::Expr>,
    inp_inp: &[Em::Expr],
    em: &mut Em)
    -> Result<(),TrErr<'b,V,Em::Error>>
    where V: 'b+Bytes<'b>+FromConst<'b>+IntValue<'b>+Vector<'b>+Pointer<'b>+FromMD<'b>+Debug,
          Cfg: TranslationCfg<Em>,
          Lib: Library<'b,V,Em>,
          Em: DeriveValues,
          Em::Expr: 'b {
    debug_assert_eq!(prog.num_elem(),prog_inp.len());
    debug_assert_eq!(inp.num_elem(),inp_inp.len());

    let (step,thr_idx) = if prog.is_single_threaded() {
        let idx = em.const_bitvec(STEP_BW,BigUint::from(0u8))?;
        (None,idx)
    } else {
        match ProgramInput::thread_activation(&thread_id,Id::new(),inp,inp_inp,em)? {
            Some((step,idx)) => (Some(step),idx),
            None => {
                let mut rinp = inp.clone();
                rinp.add_thread(thread_id.clone());
                return Err(TrErr::InputNeeded(rinp))
            }
        }
    };
    let thread_pool = Assoc::lookup(then(Id,ThreadsPath),
                                    prog,&thread_id).expect("Thread not found");
    let mut thread_iter = CompVec::access_dyn(thread_pool,
                                              prog,thr_idx,em)?;
    let mut conds = Vec::new();
    while let Some(thread) = thread_iter.next(&mut conds,0,em)? {
        cfg.change_thread_activation(&mut conds,0,em)?;
        let stack_top = then(thread.clone(),
                             StackTopPath);
        let mut stack_top_iter = Choice::choices(stack_top,prog,prog_inp,em)?;
        let cpos = conds.len();
        while let Some(context_id_p) = stack_top_iter.next(&mut conds,cpos,em)? {
            cfg.change_context_activation(&mut conds,cpos,em)?;
            // Handle only matching contexts
            let fr_id = match context_id_p.get(prog).0 {
                None => continue,
                Some(ContextId::Call(ref cid_)) => if cf_id!=*cid_ {
                    continue
                } else {
                    None
                },
                Some(ContextId::Stack(ref cid_,ref id_)) => if cf_id!=*cid_ {
                    continue
                } else {
                    Some(id_.clone())
                }
            };
            let call_stack = Assoc::lookup(then(thread.clone(),
                                                CallStackPath),
                                           prog,&cf_id)
                .expect("Call stack not found");
            let mut call_frame_iter = BitVecVectorStack::top(call_stack.clone(),
                                                             prog,prog_inp,
                                                             em)?;
            // Iterate over all active call frames
            let cpos = conds.len();
            while let Some(call_frame) = call_frame_iter.next(&mut conds,cpos,em)? {
                cfg.change_call_frame_activation(&mut conds,cpos,em)?;
                let cf = then(call_frame.clone(),
                              Element1Of2);
                let acts = then(cf.clone(),
                                ActivationPath);

                match Choice::find(acts.clone(),prog,prog_inp,
                                   |p,from,_,_| Ok(p.get(from).0 == instr_id),
                                   em)? {
                    None => {
                        println!("Activation not found: {:?}",instr_id);
                        continue
                    },
                    Some(act) => {
                        conds.push(Choice::is_selected(&act,prog,prog_inp,em)?);
                    }
                }
                cfg.change_instr_activation(&mut conds,cpos,em)?;
                match instr.content {
                    llvm_ir::InstructionC::Alloca(ref name,ref tp,ref sz,_) => {
                        let mut dyn_inp = Vec::new();
                        let dyn = match sz {
                            &None => None,
                            &Some(ref sz) => Some(translate_value(
                                &m.datalayout,&sz.val,&sz.tp,&m.types,
                                &cf,prog,prog_inp,
                                &mut dyn_inp,em)?)
                        };
                        let stat_bits = m.datalayout
                            .type_size_in_bits(tp,&m.types);
                        let stat_bytes = (stat_bits/8) as usize;
                        let mut sl_inp = Vec::new();
                        let sl = match dyn {
                            None => MemSlice::alloca(stat_bytes,&mut sl_inp,em)?,
                            Some(_) => panic!("Dynamic sized allocations not supported")
                        };
                        let mut ptr_inp = Vec::new();
                        let mut ptr = Choice::empty(&mut ptr_inp,em)?;

                        match fr_id {
                            None => {
                                let fr = then(call_frame.clone(),
                                              Element2Of2);
                                let allocs = then(fr,
                                                  AllocationsPath);
                                let alloc_pool = match Assoc::lookup(
                                    allocs.clone(),prog,&instr_id) {
                                    None => {
                                        let mut pool_inp = Vec::new();
                                        let pool = CompVec::new(&mut pool_inp,
                                                                em)?;
                                        let alloc_idx = Assoc::insert(&allocs,prog,prog_inp,
                                                                      instr_id,pool,&mut pool_inp,
                                                                      em)?;
                                        then(allocs,alloc_idx)
                                    },
                                    Some(p) => p
                                };
                                let alloc_idx = CompVec::alloc(&alloc_pool,
                                                               prog,prog_inp,
                                                               sl,&mut sl_inp,
                                                               &|_,_,_,_| Ok(false),em)?;

                                // Generate the new pointer target
                                let mut trg_inp = Vec::new();
                                let thread_idx = em.const_bitvec(INDEX_WIDTH,BigUint::from(thread.then.0))?;
                                let fr_idx = em.const_bitvec(INDEX_WIDTH,BigUint::from(call_frame.then.0))?;
                                let alloc_idx = em.const_bitvec(INDEX_WIDTH,BigUint::from(alloc_idx.0))?;
                                let trg = PointerTrg::stack(thread_id,
                                                            thread_idx,
                                                            FrameId::Call(cf_id),
                                                            fr_idx,
                                                            instr_id,
                                                            alloc_idx,
                                                            &mut trg_inp,
                                                            em)?;
                                
                                let rcond = if conds.len()==0 {
                                    em.const_bool(true)?
                                } else {
                                    em.and(conds.clone())?
                                };

                                Choice::insert(&Id::new(),&mut ptr,&mut ptr_inp,
                                               (trg,(Data((stat_bytes,0)),None)),
                                               &mut trg_inp,rcond,em)?;
                            },
                            Some(_) => unimplemented!()
                        }
                        let mut val_inp = Vec::new();
                        let val = V::from_pointer(
                            m.datalayout.pointer_alignment(0).0 as usize,
                            &Id::new(),&ptr,&ptr_inp[..],
                            &mut val_inp,em)?;
                        // Insert the pointer
                        let values = then(cf.clone(),
                                          ValuesPath);
                        match Assoc::lookup(values.clone(),
                                            prog,&name) {
                            None => {
                                Assoc::insert(&values,prog,prog_inp,
                                              name,val,&mut val_inp,em)?;
                            },
                            Some(old_ptr) => {
                                let rcond = if conds.len()==0 {
                                    em.const_bool(true)?
                                } else {
                                    em.and(conds.clone())?
                                };
                                if !old_ptr.set_cond(prog,prog_inp,
                                                     val,&mut val_inp,
                                                     &rcond,em)? {
                                    panic!("Cannot merge new value")
                                }
                            }
                        }
                        update_activation(
                            &acts,prog,prog_inp,&conds,instr_id.next(),em
                        )?;
                    },
                    llvm_ir::InstructionC::Call(ref ret,_,ref ret_tp,ref called,ref args,_) => {
                        // Create the function type of the call
                        let arg_tps = args.iter().map(|v| v.tp.clone()).collect();
                        let ftp = llvm_ir::types::Type::Function(match ret_tp {
                            &Some((ref t,_)) => Some(Box::new(t.clone())),
                            &None => None
                        },arg_tps,false);
                        // Update instruction activation
                        update_activation(
                            &acts,prog,prog_inp,&conds,instr_id.next(),em
                        )?;
                        // Translate the called value
                        let mut rcalled_inp = Vec::new();
                        let rcalled = translate_value(
                            &m.datalayout,called,&ftp,&m.types,
                            &cf,prog,prog_inp,
                            &mut rcalled_inp,em)?;
                        let mut base_inp = Vec::new();
                        let base = V::to_pointer(&Id::new(),
                                                 &rcalled,&rcalled_inp[..],
                                                 &mut base_inp,em)?
                        .expect("Called value not a pointer");
                        let mut trgs = Choice::choices(
                            Id::new(),&base,&base_inp[..],em
                        )?;
                        let cpos = conds.len();
                        while let Some(trg) = trgs.next(&mut conds,cpos,em)? {
                            match trg.get(&base) {
                                &(PointerTrg::Global(name),_) => {
                                    let mut targs_inp = Vec::new();
                                    let mut targs = CompVec::with_capacity(
                                        args.len(),&mut targs_inp,em)?;
                                    let mut targ_inp = Vec::new();
                                    for arg in args.iter() {
                                        targ_inp.clear();
                                        let targ = translate_value(
                                            &m.datalayout,&arg.val,&arg.tp,&m.types,
                                            &cf,prog,prog_inp,
                                            &mut targ_inp,em)?;
                                        CompVec::push(&Id::new(),
                                                      &mut targs,&mut targs_inp,
                                                      targ,&mut targ_inp,em)?;
                                    }
                                    let ret_path = match ret {
                                        &None => None,
                                        &Some(ref rname)
                                            => Some((then(cf.clone(),
                                                          ValuesPath),rname))
                                    };
                                    let cpos = conds.len();
                                    let implemented = lib.call(name,
                                                               &Id::new(),&targs,&targs_inp[..],
                                                               ret_path,
                                                               &m.datalayout,
                                                               instr_id,
                                                               prog,prog_inp,
                                                               &mut conds,
                                                               em)?;
                                    cfg.change_instr_not_blocking(&mut conds,cpos,em)?;
                                    if !implemented {
                                        // Create a new call frame
                                        let cfun = m.functions.get(name).expect("Cannot find called function");
                                        let cblk = match cfun.body {
                                            None => panic!("Called function has no body: {}",cfun.name),
                                            Some(ref bdy) => &bdy[0].name
                                        };
                                        let nxt_instr = InstructionRef { function: &cfun.name,
                                                                         basic_block: cblk,
                                                                         instruction: 0 };
                                        let mut nframe_inp = Vec::new();
                                        let nframe = tuple(
                                            |res,em| CallFrame::construct(
                                                Assoc::empty,
                                                |res,em| CompVec::construct(
                                                    args.iter(),
                                                    |arg,res,em| translate_value(&m.datalayout,&arg.val,&arg.tp,
                                                                                 &m.types,
                                                                                 &cf,prog,&prog_inp[..],
                                                                                 res,em),
                                                    res,em),
                                                |res,em| Choice::singleton(|_,_| Ok(Data(nxt_instr)),res,em),
                                                Choice::empty,
                                                res,em),
                                            |res,em| Frame::construct(
                                                |res,em| Choice::singleton(|_,_| Ok(context_id_p.get(prog).clone()),res,em),
                                                Assoc::empty,
                                                res,em),
                                            &mut nframe_inp,em)?;
                                        // Insert the call frame
                                        let ncall_id = (Some(instr_id),name);
                                        let (stack_exists,ncall_stack) = Assoc::lookup_or_insert(
                                            then(thread.clone(),
                                                 CallStackPath),
                                            prog,prog_inp,ncall_id,
                                            |res,em| BitVecVectorStack::singleton(INDEX_WIDTH,
                                                                                  |res,em| {
                                                                                      swap(res,&mut nframe_inp);
                                                                                      Ok(nframe.clone())
                                                                                  },res,em),
                                            em)?;
                                        BitVecVectorStack::push(&ncall_stack,prog,prog_inp,
                                                                &mut conds,&nframe,&nframe_inp,
                                                                em)?;
                                        // Update the stack top
                                        let stack_top = then(thread.clone(),
                                                             StackTopPath);
                                        let rcond = if conds.len()==0 {
                                            em.const_bool(true)?
                                        } else {
                                            em.and(conds.clone())?
                                        };
                                        Choice::set_chosen(&stack_top,prog,prog_inp,
                                                           Data(Some(ContextId::Call(ncall_id))),
                                                           &mut Vec::new(),rcond,em)?;
                                    }
                                },
                                _ => unimplemented!()
                            }
                        }
                    },
                    llvm_ir::InstructionC::Unary(ref name,ref arg,ref op) => {
                        // Update instruction activation
                        update_activation(
                            &acts,prog,prog_inp,&conds,instr_id.next(),em
                        )?;
                        let mut rarg_inp = Vec::new();
                        let rarg = translate_value(&m.datalayout,&arg.val,&arg.tp,&m.types,
                                                   &cf,prog,prog_inp,&mut rarg_inp,em)?;
                        match op {
                            &llvm_ir::UnaryInst::Cast(ref tp,ref op) => match op {
                                &llvm_ir::CastInst::Bitcast => {
                                    // Pointer casts are ignored, just copy the argument
                                    let rcond = if conds.len()==0 {
                                        em.const_bool(true)?
                                    } else {
                                        em.and(conds.clone())?
                                    };
                                    Assoc::insert_cond(then(cf.clone(),
                                                            ValuesPath),
                                                       prog,prog_inp,name,rarg,&mut rarg_inp,
                                                       &rcond,em)?;
                                },
                                &llvm_ir::CastInst::SExt => {
                                    let nsz = match tp {
                                        &llvm_ir::types::Type::Int(w) => w,
                                        _ => panic!("sext target not an int")
                                    };
                                    let mut nval_inp = Vec::new();
                                    let nval = V::sext(&Id::new(),&rarg,&rarg_inp[..],
                                                       nsz as usize,&mut nval_inp,em)?;
                                    let rcond = if conds.len()==0 {
                                        em.const_bool(true)?
                                    } else {
                                        em.and(conds.clone())?
                                    };
                                    Assoc::insert_cond(then(cf.clone(),
                                                            ValuesPath),
                                                       prog,prog_inp,name,nval,&mut nval_inp,
                                                       &rcond,em)?;
                                },
                                &llvm_ir::CastInst::ZExt => {
                                    let nsz = match tp {
                                        &llvm_ir::types::Type::Int(w) => w,
                                        _ => panic!("zext target not an int")
                                    };
                                    let mut nval_inp = Vec::new();
                                    let nval = V::zext(&Id::new(),&rarg,&rarg_inp[..],
                                                       nsz as usize,&mut nval_inp,em)?;
                                    let rcond = if conds.len()==0 {
                                        em.const_bool(true)?
                                    } else {
                                        em.and(conds.clone())?
                                    };
                                    Assoc::insert_cond(then(cf.clone(),
                                                            ValuesPath),
                                                       prog,prog_inp,name,nval,&mut nval_inp,
                                                       &rcond,em)?;
                                },
                                &llvm_ir::CastInst::Trunc => {
                                    let nsz = match tp {
                                        &llvm_ir::types::Type::Int(w) => w,
                                        _ => panic!("trunc target not an int")
                                    };
                                    let mut nval_inp = Vec::new();
                                    let nval = V::trunc(&Id::new(),&rarg,&rarg_inp[..],
                                                        nsz as usize,&mut nval_inp,em)?;
                                    let rcond = if conds.len()==0 {
                                        em.const_bool(true)?
                                    } else {
                                        em.and(conds.clone())?
                                    };
                                    Assoc::insert_cond(then(cf.clone(),
                                                            ValuesPath),
                                                       prog,prog_inp,name,nval,&mut nval_inp,
                                                       &rcond,em)?;
                                },
                                &llvm_ir::CastInst::IntToPtr => {
                                    // Pointer casts are ignored, just copy the argument
                                    let rcond = if conds.len()==0 {
                                        em.const_bool(true)?
                                    } else {
                                        em.and(conds.clone())?
                                    };
                                    Assoc::insert_cond(then(cf.clone(),
                                                            ValuesPath),
                                                       prog,prog_inp,name,rarg,&mut rarg_inp,
                                                       &rcond,em)?;
                                },
                                &llvm_ir::CastInst::PtrToInt => {
                                    // Pointer casts are ignored, just copy the argument
                                    let rcond = if conds.len()==0 {
                                        em.const_bool(true)?
                                    } else {
                                        em.and(conds.clone())?
                                    };
                                    Assoc::insert_cond(then(cf.clone(),
                                                            ValuesPath),
                                                       prog,prog_inp,name,rarg,&mut rarg_inp,
                                                       &rcond,em)?;
                                },
                                _ => panic!("Unsupported cast: {:?}",op)
                            },
                            &llvm_ir::UnaryInst::Load(_,_) => {
                                let sz = match arg.tp {
                                    llvm_ir::types::Type::Pointer(ref tp_,_)
                                        => (m.datalayout.type_size_in_bits(tp_,&m.types)/8) as usize,
                                    _ => panic!("Load argument not a pointer")
                                };
                                let mut ptr_inp = Vec::new();
                                let ptr = match V::to_pointer(&Id::new(),&rarg,&rarg_inp[..],
                                                              &mut ptr_inp,em)? {
                                    None => panic!("Load argument isn't a pointer"),
                                    Some(r) => r
                                };
                                let mut bases = Choice::choices(Id::new(),&ptr,&ptr_inp[..],em)?;
                                let cpos = conds.len();
                                while let Some(base) = bases.next(&mut conds,cpos,em)? {
                                    let trg = then(base.clone(),
                                                   Element1Of2);
                                    let off = then(base,Element2Of2);
                                    let mut lookups = MemLookups::new(&trg,&ptr,&ptr_inp[..],prog,prog_inp,em)?;
                                    let cpos = conds.len();
                                    while let Some(lookup) = lookups.next(&mut conds,cpos,prog,prog_inp,em)? {
                                        let mut load_inp = Vec::new();
                                        let load = lookup.load(
                                            &m.datalayout,
                                            &off,&ptr,&ptr_inp[..],
                                            sz,prog,prog_inp,
                                            &mut load_inp,em)?;
                                        let rcond = if conds.len()==0 {
                                            em.const_bool(true)?
                                        } else {
                                            em.and(conds.clone())?
                                        };
                                        Assoc::insert_cond(then(cf.clone(),ValuesPath),
                                                           prog,prog_inp,name,load,&mut load_inp,
                                                           &rcond,em)?;
                                    }
                                }
                            }
                        }
                    },
                    llvm_ir::InstructionC::Select(ref name,ref sel,ref tp,ref if_t,ref if_f) => {
                        // Update instruction activation
                        update_activation(
                            &acts,prog,prog_inp,&conds,instr_id.next(),em
                        )?;
                        let sel_tp = llvm_ir::types::Type::Int(1);
                        let mut rsel_inp = Vec::new();
                        let rsel = translate_value(&m.datalayout,sel,&sel_tp,&m.types,
                                                   &cf,prog,prog_inp,&mut rsel_inp,em)?;
                        let cond = V::to_bool(&Id,&rsel,&rsel_inp[..],em)?;
                        let mut rif_t_inp = Vec::new();
                        let rif_t = translate_value(&m.datalayout,if_t,tp,&m.types,
                                                    &cf,prog,prog_inp,&mut rif_t_inp,em)?;
                        let mut rif_f_inp = Vec::new();
                        let rif_f = translate_value(&m.datalayout,if_f,tp,&m.types,
                                                    &cf,prog,prog_inp,&mut rif_f_inp,em)?;
                        let mut res_inp = Vec::new();
                        let res = ite(&cond,
                                      &Id,&rif_t,&rif_t_inp[..],
                                      &Id,&rif_f,&rif_f_inp[..],
                                      &mut res_inp,em)?.expect("Cannot merge for select");
                        // Insert the result
                        let rcond = if conds.len()==0 {
                            em.const_bool(true)?
                        } else {
                            em.and(conds.clone())?
                        };
                        Assoc::insert_cond(then(cf.clone(),
                                                ValuesPath),
                                           prog,prog_inp,name,res,&mut res_inp,
                                           &rcond,em)?;
                    },
                    llvm_ir::InstructionC::GEP(ref name,llvm_ir::GEP {
                        ref ptr,ref indices,..
                    }) => {
                        // Update instruction activation
                        update_activation(
                            &acts,prog,prog_inp,&conds,instr_id.next(),em
                        )?;
                        // Calculate the GEP
                        let mut rptr_inp = Vec::new();
                        let rptr = translate_value(
                            &m.datalayout,&ptr.val,&ptr.tp,&m.types,
                            &cf,prog,prog_inp,&mut rptr_inp,em)?;
                        let bw = rptr.byte_width();
                        let mut base_inp = Vec::new();
                        let mut base = V::to_pointer(&Id,&rptr,&rptr_inp[..],
                                                     &mut base_inp,em)?
                        .expect("GEP base not a pointer");
                        let mut idx_inp = Vec::new();
                        let mut idx = CompVec::with_capacity(indices.len(),&mut idx_inp,em)?;
                        let mut cur_tp = &ptr.tp;
                        for &(ref el,_) in indices.iter() {
                            cur_tp = match resolve_tp(cur_tp,&m.types) {
                                &Type::Struct(ref sub_tps) => match el.val {
                                    llvm_ir::Value::Constant(
                                        llvm_ir::Constant::Int(ref c)) => {
                                        let rc = c.to_usize().unwrap();
                                        let mut coff = 0;
                                        for sub_tp in sub_tps.iter().take(rc) {
                                            coff += m.datalayout
                                                .type_size_in_bits(sub_tp,
                                                                   &m.types)/8;
                                        }
                                        CompVec::push(&Id,&mut idx,&mut idx_inp,
                                                      (None,Data(coff as usize)),
                                                      &mut Vec::new(),em)?;
                                        &sub_tps[rc];
                                        break
                                    },
                                    _ => panic!("Struct not indexed by int")
                                },
                                &Type::Pointer(ref ptr_tp,_) => {
                                    let sz = m.datalayout.type_size_in_bits(
                                        ptr_tp,&m.types)/8;
                                    let mut i_inp = Vec::new();
                                    let i = translate_value(
                                        &m.datalayout,
                                        &el.val,&el.tp,
                                        &m.types,
                                        &cf,prog,prog_inp,
                                        &mut i_inp,em)?;
                                    let mut off_inp = Vec::new();
                                    let off = V::to_offset(&Id,&i,&i_inp[..],&mut off_inp,em)?;
                                    let off_e = Singleton::get(&Id,&off,&off_inp[..],em)?;
                                    match em.derive_const(&off_e)? {
                                        None => panic!("Dynamic GEP"),//idx.push((Some((off,off_inp)),sz as usize)),
                                        Some(off_c) => CompVec::push(&Id,&mut idx,&mut idx_inp,
                                                                     (None,Data(value_as_index(&off_c)*(sz as usize))),
                                                                     &mut Vec::new(),em)?
                                    };
                                    ptr_tp
                                },
                                &Type::Array(_,ref el_tp) => {
                                    let sz = m.datalayout.type_size_in_bits(
                                        el_tp,&m.types)/8;
                                    let mut i_inp = Vec::new();
                                    let i = translate_value(
                                        &m.datalayout,
                                        &el.val,&el.tp,
                                        &m.types,
                                        &cf,prog,prog_inp,
                                        &mut i_inp,em)?;
                                    let mut off_inp = Vec::new();
                                    let off = V::to_offset(&Id,&i,&i_inp[..],&mut off_inp,em)?;
                                    let off_e = Singleton::get(&Id,&off,&off_inp[..],em)?;
                                    match em.derive_const(&off_e)? {
                                        None => CompVec::push(&Id,&mut idx,&mut idx_inp,
                                                              (Some(off),Data(sz as usize)),
                                                              &mut off_inp,em)?,
                                        Some(off_c) => CompVec::push(&Id,&mut idx,&mut idx_inp,
                                                                     (None,Data(value_as_index(&off_c)*(sz as usize))),
                                                                     &mut Vec::new(),em)?
                                    };
                                    el_tp
                                },
                                _ => panic!("GEP for {:?}",cur_tp)
                            };
                        }
                        base_pointer_gep(
                            Id,&mut base,&mut base_inp,
                            &Id,&idx,&idx_inp[..],em)?;
                        let mut nptr_inp = Vec::new();
                        let nptr = V::from_pointer(
                            bw,&Id,&base,&base_inp[..],
                            &mut nptr_inp,em)?;
                        // Write the pointer
                        let rcond = if conds.len()==0 {
                            em.const_bool(true)?
                        } else {
                            em.and(conds.clone())?
                        };
                        Assoc::insert_cond(then(cf.clone(),
                                                ValuesPath),
                                           prog,prog_inp,name,nptr,&mut nptr_inp,
                                           &rcond,em)?;
                    },
                    llvm_ir::InstructionC::Store(_,ref val,ref ptr,_) => {
                        // Update instruction activation
                        update_activation(
                            &acts,prog,prog_inp,&conds,instr_id.next(),em
                        )?;
                        let mut rptr_inp_ = Vec::new();
                        let rptr_ = translate_value(&m.datalayout,&ptr.val,&ptr.tp,
                                                    &m.types,
                                                    &cf,prog,prog_inp,
                                                    &mut rptr_inp_,em)?;
                        let mut rptr_inp = Vec::new();
                        let rptr = match V::to_pointer(
                            &Id,&rptr_,&rptr_inp_[..],&mut rptr_inp,em)? {
                            None => panic!("Store target isn't a pointer"),
                            Some(r) => r
                        };
                        let mut rval_inp = Vec::new();
                        let rval = translate_value(&m.datalayout,&val.val,&val.tp,
                                                   &m.types,
                                                   &cf,prog,prog_inp,
                                                   &mut rval_inp,em)?;

                        let mut bases = Choice::choices(Id,&rptr,&rptr_inp[..],em)?;
                        let cpos = conds.len();
                        while let Some(base) = bases.next(&mut conds,cpos,em)? {
                            let trg = then(base.clone(),
                                           Element1Of2);
                            let off = then(base,Element2Of2);
                            let mut lookups = MemLookups::new(&trg,&rptr,
                                                              &rptr_inp[..],
                                                              prog,prog_inp,em)?;
                            let cpos = conds.len();
                            while let Some(lookup) = lookups.next(&mut conds,cpos,prog,prog_inp,em)? {
                                //println!("STORE LOOKUP");
                                let rcond = if conds.len()==0 {
                                    None
                                } else {
                                    Some(em.and(conds.clone())?)
                                };
                                lookup.store(&off,&rptr,&rptr_inp[..],
                                             rval.clone(),&mut rval_inp.clone(),
                                             prog,prog_inp,rcond,em)?;
                            }
                        }
                    },
                    llvm_ir::InstructionC::Bin(ref name,ref op,ref tp,ref lhs,ref rhs) => {
                        // Update instruction activation
                        update_activation(
                            &acts,prog,prog_inp,&conds,instr_id.next(),em
                        )?;
                        let mut val_l_inp = Vec::new();
                        let val_l = translate_value(&m.datalayout,
                                                    lhs,tp,
                                                    &m.types,
                                                    &cf,prog,prog_inp,
                                                    &mut val_l_inp,em)?;
                        let mut val_r_inp = Vec::new();
                        let val_r = translate_value(&m.datalayout,
                                                    rhs,tp,
                                                    &m.types,
                                                    &cf,prog,prog_inp,
                                                    &mut val_r_inp,em)?;
                        let mut res_inp = Vec::new();
                        let res = V::bin(op,
                                         &Id,&val_l,&val_l_inp[..],
                                         &Id,&val_r,&val_r_inp[..],
                                         &mut res_inp,em)?;
                        let rcond = if conds.len()==0 {
                            em.const_bool(true)?
                        } else {
                            em.and(conds.clone())?
                        };
                        Assoc::insert_cond(then(cf.clone(),
                                                ValuesPath),
                                           prog,prog_inp,name,res,&mut res_inp,
                                           &rcond,em)?;
                    },
                    llvm_ir::InstructionC::Term(llvm_ir::Terminator::Ret(ref retv)) => {
                        let mut rret_inp = Vec::new();
                        let rret = match retv {
                            &None => None,
                            &Some(ref r) => Some(translate_value(&m.datalayout,
                                                                 &r.val,&r.tp,
                                                                 &m.types,
                                                                 &cf,prog,prog_inp,
                                                                 &mut rret_inp,em)?)
                        };
                        match fr_id {
                            None => {
                                let prev = then(then(call_frame.clone(),
                                                     Element2Of2),
                                                PrevFramePath);
                                let mut prev_it = Choice::choices(
                                    prev,prog,&prog_inp[..],em)?;
                                match rret {
                                    None => {},
                                    Some(ret) => {
                                        let cpos = conds.len();
                                        while let Some(ctx) = prev_it.next(&mut conds,cpos,em)? {
                                            match ctx.get(prog).0.clone() {
                                                None => {
                                                    panic!("Handle thread return")
                                                },
                                                Some(ctx_) => {
                                                    let pcall = match ctx_ {
                                                        ContextId::Call(c) => c,
                                                        ContextId::Stack(c,_) => c
                                                    };
                                                    let pstack = Assoc::lookup(then(thread.clone(),
                                                                                    CallStackPath),
                                                                               prog,&pcall)
                                                        .expect("Call stack not found");
                                                    let mut pstack_it = BitVecVectorStack::top(pstack,prog,&prog_inp[..],em)?;
                                                    let cpos = conds.len();
                                                    while let Some(pcf) = pstack_it.next(&mut conds,cpos,em)? {
                                                        let ret_instr = match cf_id.0 {
                                                            Some(i) => {
                                                                let instr = i.resolve(m);
                                                                match instr.content {
                                                                    llvm_ir::InstructionC::Call(Some(ref name),_,_,_,_,_) => name,
                                                                    _ => panic!("Returned-to instruction not a call")
                                                                }
                                                            },
                                                            None => panic!("No return instruction available")
                                                        };
                                                        let ret_vals = then(then(pcf,Element1Of2),
                                                                            ValuesPath);
                                                        let rcond = if conds.len()==0 {
                                                            em.const_bool(true)?
                                                        } else {
                                                            em.and(conds.clone())?
                                                        };
                                                        Assoc::insert_cond(ret_vals,prog,prog_inp,
                                                                           ret_instr,
                                                                           ret.clone(),&mut rret_inp.clone(),
                                                                           &rcond,em)?;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                };
                                BitVecVectorStack::pop(&call_stack,
                                                       prog,prog_inp,
                                                       &conds,em)?;
                            },
                            Some(_) => unimplemented!()
                        }
                    },
                    llvm_ir::InstructionC::ICmp(ref name,ref op,ref tp,ref lhs,ref rhs) => {
                        // Update instruction activation
                        update_activation(
                            &acts,prog,prog_inp,&conds,instr_id.next(),em
                        )?;
                        let mut vl_inp = Vec::new();
                        let vl = translate_value(&m.datalayout,
                                                 lhs,tp,
                                                 &m.types,
                                                 &cf,prog,prog_inp,
                                                 &mut vl_inp,em)?;
                        let mut vr_inp = Vec::new();
                        let vr = translate_value(&m.datalayout,
                                                 rhs,tp,
                                                 &m.types,
                                                 &cf,prog,prog_inp,
                                                 &mut vr_inp,em)?;
                        let cond = V::icmp(op,
                                           &Id,&vl,&vl_inp[..],
                                           &Id,&vr,&vr_inp[..],em)?;
                        let mut ret_inp = Vec::new();
                        let ret = V::from_bool(cond,&mut ret_inp,em)?;
                        let rcond = if conds.len()==0 {
                            em.const_bool(true)?
                        } else {
                            em.and(conds.clone())?
                        };
                        Assoc::insert_cond(then(cf.clone(),
                                                ValuesPath),
                                           prog,prog_inp,name,ret,&mut ret_inp,
                                           &rcond,em)?;
                    },
                    llvm_ir::InstructionC::Term(llvm_ir::Terminator::BrC(ref cond,ref trgT,ref trgF)) => {
                        let instrT = InstructionRef { function: instr_id.function,
                                                      basic_block: trgT,
                                                      instruction: 0 };
                        let instrF = InstructionRef { function: instr_id.function,
                                                      basic_block: trgF,
                                                      instruction: 0 };
                        
                        let tp = llvm_ir::types::Type::Int(1);
                        let mut rcond_inp = Vec::new();
                        let rcond = translate_value(&m.datalayout,
                                                    cond,&tp,
                                                    &m.types,
                                                    &cf,prog,prog_inp,
                                                    &mut rcond_inp,em)?;
                        let bcond = V::to_bool(&Id,&rcond,&rcond_inp[..],em)?;
                        let mut ch_inp = Vec::new();
                        let mut ch = Choice::empty(&mut ch_inp,em)?;
                        Choice::insert(&Id,&mut ch,&mut ch_inp,
                                       Data(instrT),&mut Vec::new(),
                                       bcond.clone(),em)?;
                        let nbcond = em.not(bcond.clone())?;
                        Choice::insert(&Id,&mut ch,&mut ch_inp,
                                       Data(instrF),&mut Vec::new(),
                                       nbcond.clone(),em)?;
                        if conds.len() == 0 {
                            acts.set(prog,prog_inp,ch,&mut ch_inp,em)?;
                        } else {
                            let ccond = em.and(conds.clone())?;
                            if !acts.set_cond(prog,prog_inp,ch,&mut ch_inp,&ccond,em)? {
                                panic!("Failed to set activation")
                            }
                        }                        
                        // Evaluate phis
                        let phi = then(cf.clone(),
                                       PhiPath);
                        let mut nphi_inp = Vec::new();
                        let mut nphi = Choice::empty(&mut nphi_inp,em)?;

                        Choice::insert(&Id,&mut nphi,&mut nphi_inp,
                                       Data((instr_id.basic_block,trgT)),
                                       &mut Vec::new(),bcond.clone(),em)?;
                        Choice::insert(&Id,&mut nphi,&mut nphi_inp,
                                       Data((instr_id.basic_block,trgF)),
                                       &mut Vec::new(),nbcond.clone(),em)?;
                        if conds.len()==0 {
                            phi.set(prog,prog_inp,nphi,&mut nphi_inp,em)?;
                        } else {
                            let ccond = em.and(conds.clone())?;
                            if !phi.set_cond(prog,prog_inp,nphi,&mut nphi_inp,&ccond,em)? {
                                panic!("Failed to set phi")
                            }
                        }
                    },
                    llvm_ir::InstructionC::Term(llvm_ir::Terminator::Br(ref trg)) => {
                        let instr_next = InstructionRef { function: instr_id.function,
                                                          basic_block: trg,
                                                          instruction: 0 };
                        // Update instruction activation
                        update_activation(&acts,prog,prog_inp,
                                          &conds,instr_next,em)?;
                        // Evaluate phis
                        let phi = then(cf.clone(),
                                       PhiPath);

                        let mut nphi_inp = Vec::new();
                        let nphi = Choice::singleton(
                            |_,_| Ok(Data((instr_id.basic_block,trg))),
                            &mut nphi_inp,em)?;

                        if conds.len()==0 {
                            phi.set(prog,prog_inp,nphi,&mut nphi_inp,em)?;
                        } else {
                            let ccond = em.and(conds.clone())?;
                            if !phi.set_cond(prog,prog_inp,nphi,&mut nphi_inp,&ccond,em)? {
                                panic!("Failed to set phi")
                            }
                        }
                    },
                    llvm_ir::InstructionC::Phi(ref name,ref tp,ref srcs) => {
                        // Update instruction activation
                        update_activation(
                            &acts,prog,prog_inp,&conds,instr_id.next(),em
                        )?;

                        // Update value
                        let phi = then(cf.clone(),
                                       PhiPath);
                        let mut rval_inp = Vec::new();
                        let mut rval = None;
                        let mut nval_inp = Vec::new();
                        let mut res_inp = Vec::new();
                        for &(ref val,ref src) in srcs.iter() {
                            if let Some(el) = Choice::find(
                                phi.clone(),prog,&prog_inp[..],
                                |el,from,_,_| {
                                    let &Data((ref csrc,ref blk)) = el.get(from);
                                    Ok(*csrc==src &&
                                       *blk==instr_id.basic_block)
                                },em)? {

                                nval_inp.clear();
                                let nval = translate_value(
                                    &m.datalayout,
                                    val,tp,
                                    &m.types,
                                    &cf,prog,prog_inp,&mut nval_inp,em)?;
                                let mut nconds = conds.clone();
                                let sel = Choice::is_selected(
                                    &el,prog,prog_inp,em)?;
                                nconds.push(sel);
                                let rcond = em.and(nconds)?;
                                rval = match rval {
                                    None => {
                                        swap(&mut rval_inp,&mut nval_inp);
                                        Some(nval)
                                    },
                                    Some(cval) => {
                                        res_inp.clear();
                                        let res = ite(&rcond,
                                                      &Id,&nval,&nval_inp[..],
                                                      &Id,&cval,&rval_inp[..],
                                                      &mut res_inp,em)?
                                        .expect("Cannot merge phis");
                                        Some(res)
                                    }
                                };
                            }
                        }
                        let rcond = if conds.len()==0 {
                            em.const_bool(true)?
                        } else {
                            em.and(conds.clone())?
                        };
                        Assoc::insert_cond(then(cf.clone(),
                                                ValuesPath),
                                           prog,prog_inp,name,
                                           rval.unwrap(),&mut rval_inp,
                                           &rcond,em)?;
                    },
                    _ => panic!("Cannot translate instruction {:#?}",instr)
                }
            }
        }
    }
    Ok(())
}

pub fn translate_value<'b,FromCf,Cf,V,Em>(
    dl: &'b DataLayout,
    value: &'b llvm_ir::Value,
    tp: &Type,
    tps: &'b HashMap<String,Type>,
    cf: &Cf,
    cf_from: &FromCf,
    cf_arr: &[Em::Expr],
    res: &mut Vec<Em::Expr>,
    em: &mut Em)
    -> Result<V,Em::Error>
    where Cf: Path<'b,Em,FromCf,To=CallFrame<'b,V>>,
          V: 'b+Bytes<'b>+FromConst<'b>+Pointer<'b>+IntValue<'b>+Vector<'b>+FromMD<'b>+Clone,
          Em: DeriveValues {
    match value {
        &llvm_ir::Value::Constant(ref c)
            => translate_constant(dl,c,tp,tps,res,em),
        &llvm_ir::Value::Local(ref name) => {
            let val_path = Assoc::lookup(then(cf.clone(),
                                              ValuesPath),
                                         cf_from,&name)
                .expect("Cannot find variable");
            let val = val_path.get(cf_from).clone();
            val_path.read_into(cf_from,0,val.num_elem(),cf_arr,res,em)?;
            Ok(val)
        },
        &llvm_ir::Value::Argument(n) => {
            let arg_path = then(then(cf.clone(),
                                     ArgumentsPath),
                                CompVecP(n));
            let arg = arg_path.get(cf_from).clone();
            arg_path.read_into(cf_from,0,arg.num_elem(),cf_arr,res,em)?;
            Ok(arg)
        },
        &llvm_ir::Value::Metadata(ref md) => V::from_md(md,res,em),
        _ => panic!("Translate value: {:#?}",value)
    }
}

pub fn translate_constant<'b,V,Em>(dl: &'b DataLayout,
                                   c: &'b llvm_ir::Constant,
                                   tp: &Type,
                                   mp: &HashMap<String,Type>,
                                   res: &mut Vec<Em::Expr>,
                                   em: &mut Em)
                                   -> Result<V,Em::Error>
    where V: 'b+Bytes<'b>+Pointer<'b>+IntValue<'b>+Vector<'b>+Clone, Em: Embed {

    match c {
        &llvm_ir::Constant::Global(ref glb) => {
            let mult = match tp {
                &Type::Pointer(ref ptp,_) => match **ptp {
                    Type::Array(_,ref atp) => dl.type_size_in_bits(atp,mp)/8,
                    _ => dl.type_size_in_bits(ptp,mp)/8
                },
                &Type::Function(_,_,_) => 0,
                _ => panic!("Global pointer has wrong type {:?}",tp)
            };
            let mut inp_ptr = Vec::new();
            let ptr = base_pointer_global(mult as usize,glb,&mut inp_ptr,em)?;
            let (bw,_,_) = dl.pointer_alignment(0);
            let rptr = V::from_pointer((bw/8) as usize,
                                       &Id::new(),&ptr,&inp_ptr[..],
                                       res,em)?;
            Ok(rptr)
        },
        &llvm_ir::Constant::Int(ref val) => match tp {
            &Type::Int(bw) => {
                let rval = match val.to_biguint() {
                    Some(r) => r,
                    None => match (-val).to_biguint() {
                        Some(neg_val) => BigUint::from(1u8).shl(bw as usize) - neg_val,
                        None => unreachable!()
                    }
                };
                V::const_int(bw,rval,res,em)
            },
            _ => panic!("Integer value with non-integer type")
        },
        &llvm_ir::Constant::Array(ref arr) => {
            let mut varr: Vec<V> = Vec::with_capacity(arr.len());
            let el_tp = match tp {
                &Type::Array(_,ref subtp) => subtp,
                _ => panic!("Array value with non-array type")
            };
            for el in arr.iter() {
                let val = translate_constant(dl,el,el_tp,mp,res,em)?;
                varr.push(val);
            }
            V::vector(varr,res,em)
        },
        &llvm_ir::Constant::GEP(ref gep) => {
            let mut cur_tp = &gep.ptr.tp;
            let mut rgep_inp = Vec::new();
            let mut rgep = CompVec::with_capacity(gep.indices.len(),
                                                  &mut rgep_inp,em)?;
            for &(ref el,_) in gep.indices.iter() {
                cur_tp = match cur_tp {
                    &Type::Struct(ref sub_tps) => match el.val {
                        llvm_ir::Constant::Int(ref idx) => {
                            let ridx = match idx.to_usize() {
                                None => panic!("Index overflow"),
                                Some(i) => i
                            };
                            let mut coff = 0;
                            for sub_tp in sub_tps.iter().take(ridx) {
                                coff += dl.type_size_in_bits(sub_tp,mp)/8;
                            }
                            CompVec::push(&Id::new(),&mut rgep,&mut rgep_inp,
                                          (None,Data(coff as usize)),
                                          &mut Vec::new(),em)?;
                            &sub_tps[ridx]
                        },
                        _ => panic!("Struct not indexed by constant int")
                    },
                    &Type::Pointer(ref ptr_tp,_) => {
                        let sz = dl.type_size_in_bits(ptr_tp,mp)/8;
                        match el.val {
                            llvm_ir::Constant::Int(ref idx) => {
                                CompVec::push(&Id::new(),&mut rgep,&mut rgep_inp,
                                              (None,Data(idx.to_usize().unwrap()*(sz as usize))),
                                              &mut Vec::new(),em)?;
                            },
                            _ => panic!("Pointer not indexed properly")
                        }
                        /*let (idx,idx_inp) = translate_constant(dl,&el.val,&el.tp,mp,em)?;
                        let (off,off_inp) = V::to_offset(OptRef::Owned(idx),idx_inp);
                        let off_e = off_inp.get(&[][..],0,em)?;
                        let item = match em.derive_const(&off_e)? {
                            None => unreachable!(),
                            Some(off_c) => (None,value_as_index(&off_c)*(sz as usize))
                        };
                        res.push(item);*/
                        ptr_tp
                    },
                    &Type::Array(_,ref sub_tp) => {
                        let sz = dl.type_size_in_bits(sub_tp,mp)/8;
                        match el.val {
                            llvm_ir::Constant::Int(ref idx) => {
                                CompVec::push(&Id::new(),&mut rgep,&mut rgep_inp,
                                              (None,Data(idx.to_usize().unwrap()*(sz as usize))),
                                              &mut Vec::new(),em)?;
                            },
                            _ => panic!("Array not indexed properly")
                        }
                        sub_tp
                    },
                    _ => unimplemented!()
                }
            }
            let mut base_inp = Vec::new();
            let base: V = translate_constant(dl,&gep.ptr.val,&gep.ptr.tp,mp,
                                             &mut base_inp,em)?;
            let bw = base.byte_width();
            let mut ptr_inp = Vec::new();
            let mut ptr = V::to_pointer(&Id::new(),&base,&base_inp[..],
                                        &mut ptr_inp,em)?
            .expect("Cannot convert to pointer");
            base_pointer_gep(Id::new(),&mut ptr,&mut ptr_inp,
                             &Id::new(),&rgep,&rgep_inp[..],em)?;
            V::from_pointer(bw,&Id::new(),&ptr,&ptr_inp[..],res,em)
        },
        &llvm_ir::Constant::NullPtr => {
            let bw = (dl.pointer_alignment(0).0 / 8) as usize;
            let mut base_inp = Vec::new();
            let base = base_pointer_null(&mut base_inp,em)?;
            V::from_pointer(bw,&Id::new(),&base,&base_inp[..],res,em)
        },
        _ => panic!("Cannot translate constant {:?}",c)
    }
}

fn resolve_tp<'a>(mut tp: &'a Type,tps: &'a HashMap<String,Type>) -> &'a Type {
    loop {
        tp = match tp {
            &Type::Named(ref name) => match tps.get(name) {
                Some(ref rtp) => rtp,
                None => panic!("Cannot find type {}",name)
            },
            _ => return tp
        };
    }
}

pub fn translate_global<'b,V,Em>(dl: &'b DataLayout,
                                 c: &'b llvm_ir::Constant,
                                 tp: &'b Type,
                                 mp: &'b HashMap<String,Type>,
                                 res: &mut Vec<Em::Expr>,
                                 em: &mut Em)
                                 -> Result<MemSlice<'b,V>,Em::Error>
    where V: 'b+HasSorts+Clone,
          Em: Embed {
    let mut arr = CompVec::new(res,em)?;
    translate_global_(dl,c,tp,mp,&Id::new(),&mut arr,res,em)?;
    Ok(MemSlice(arr))
}

fn translate_global_<'a,V,From,P,Em>(
    dl: &'a DataLayout,
    c: &'a llvm_ir::Constant,
    tp: &'a Type,
    mp: &'a HashMap<String,Type>,
    path: &P,
    from: &mut From,
    arr: &mut Vec<Em::Expr>,
    em: &mut Em)
    -> Result<(),Em::Error>
    where V: 'a+HasSorts+Clone,
          Em: Embed,
          P: Path<'a,Em,From,To=CompVec<MemObj<'a,V>>> {

    match c {
        &llvm_ir::Constant::Array(ref elems) => {
            let el_tp = match tp {
                &Type::Array(_,ref subtp) => subtp,
                _ => panic!("Array value with non-array type")
            };
            for el in elems.iter() {
                translate_global_(dl,el,el_tp,mp,path,from,arr,em)?;
            }
        },
        _ => {
            CompVec::push(path,from,arr,
                          MemObj::ConstObj(dl,c,tp,mp),
                          &mut Vec::new(),em)?;
        }
    }
    Ok(())
}

pub trait IntValue<'a>: Composite<'a> {
    fn const_int<Em: Embed>(u64,BigUint,&mut Vec<Em::Expr>,&mut Em)
                            -> Result<Self,Em::Error>;
    fn bin<From1,P1: Path<'a,Em,From1,To=Self>,
           From2,P2: Path<'a,Em,From2,To=Self>,
           Em: DeriveValues>(op: &llvm_ir::BinOp,
                             lhs: &P1,
                             lfrom: &From1,
                             larr: &[Em::Expr],
                             rhs: &P2,
                             rfrom: &From2,
                             rarr: &[Em::Expr],
                             res: &mut Vec<Em::Expr>,
                             em: &mut Em)
                             -> Result<Self,Em::Error>
        where Self: 'a;
    fn sext<From,P: Path<'a,Em,From,To=Self>,
            Em: Embed>(&P,&From,&[Em::Expr],usize,&mut Vec<Em::Expr>,&mut Em)
                       -> Result<Self,Em::Error>
        where Self: 'a;
    fn zext<From,P: Path<'a,Em,From,To=Self>,
            Em: Embed>(&P,&From,&[Em::Expr],usize,&mut Vec<Em::Expr>,&mut Em)
                       -> Result<Self,Em::Error>
        where Self: 'a;
    fn trunc<From,P: Path<'a,Em,From,To=Self>,
             Em: Embed>(&P,&From,&[Em::Expr],usize,&mut Vec<Em::Expr>,&mut Em)
                        -> Result<Self,Em::Error>
        where Self: 'a;
    fn icmp<From1,P1: Path<'a,Em,From1,To=Self>,
            From2,P2: Path<'a,Em,From2,To=Self>,
            Em: Embed>(&llvm_ir::CmpOp,
                       &P1,&From1,&[Em::Expr],
                       &P2,&From2,&[Em::Expr],
                       &mut Em)
                       -> Result<Em::Expr,Em::Error>
        where Self: 'a;
    fn from_bool<Em: Embed>(Em::Expr,&mut Vec<Em::Expr>,&mut Em)
                            -> Result<Self,Em::Error>;
    fn to_bool<From,P: Path<'a,Em,From,To=Self>,
               Em: Embed>(&P,&From,&[Em::Expr],&mut Em)
                          -> Result<Em::Expr,Em::Error>
        where Self: 'a;
    fn to_offset<From,P: Path<'a,Em,From,To=Self>,
                 Em: Embed>(&P,&From,&[Em::Expr],&mut Vec<Em::Expr>,&mut Em)
                            -> Result<Singleton,Em::Error>
        where Self: 'a;
    fn from_offset<From,P: Path<'a,Em,From,To=Singleton>,
                   Em: Embed>(usize,&P,&From,&[Em::Expr],
                              &mut Vec<Em::Expr>,&mut Em)
                              -> Result<Self,Em::Error>;
}

pub trait FromMD<'a>: Composite<'a> {
    fn from_md<Em: Embed>(&'a llvm_ir::Metadata,
                          &mut Vec<Em::Expr>,
                          &mut Em)
                          -> Result<Self,Em::Error>;
}

pub trait Vector<'a>: Composite<'a> {
    fn vector<Em: Embed>(Vec<Self>,&mut Vec<Em::Expr>,&mut Em)
                         -> Result<Self,Em::Error>;
}

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub enum CompValue<Ptr,V> {
    Value(V),
    Pointer(BitField<Ptr>),
    Vector(CompVec<CompValue<Ptr,V>>),
    Metadata
}

#[derive(Clone)]
pub struct CompValueValueP;
#[derive(Clone)]
pub struct CompValuePointerP;
#[derive(Clone)]
pub struct CompValueVectorP;

pub enum CompValueMeaning<Ptr: Semantic+HasSorts,V: Semantic> {
    Value(V::Meaning),
    Pointer(<BitField<Ptr> as Semantic>::Meaning),
    Vector(Box<VecMeaning<CompValueMeaning<Ptr,V>>>)
}

pub enum CompValueMeaningCtx<Ptr: Semantic+HasSorts,V: Semantic> {
    Value(V::MeaningCtx),
    Pointer(<BitField<Ptr> as Semantic>::MeaningCtx),
    Vector(Box<CompValueMeaningCtx<Ptr,V>>)
}

impl<Ptr,V> CompValue<Ptr,V> {
    pub fn value() -> CompValueValueP {
        CompValueValueP
    }
    pub fn pointer() -> CompValuePointerP {
        CompValuePointerP
    }
    pub fn vector() -> CompValueVectorP {
        CompValueVectorP
    }
}

impl<'a,Ptr: 'a,V: 'a> SimplePathEl<'a,CompValue<Ptr,V>> for CompValueValueP {
    type To = V;
    fn get<'b>(&self,from: &'b CompValue<Ptr,V>) -> &'b Self::To where 'a: 'b {
        match from {
            &CompValue::Value(ref v) => v,
            _ => panic!("CompValue not a Value")
        }
    }
    fn get_mut<'b>(&self,from: &'b mut CompValue<Ptr,V>)
                   -> &'b mut Self::To where 'a: 'b {
        match from {
            &mut CompValue::Value(ref mut v) => v,
            _ => panic!("CompValue not a Value")
        }
    }
}

impl<'a,Ptr: 'a,V: 'a> SimplePathEl<'a,CompValue<Ptr,V>> for CompValuePointerP {
    type To = BitField<Ptr>;
    fn get<'b>(&self,from: &'b CompValue<Ptr,V>) -> &'b Self::To where 'a: 'b {
        match from {
            &CompValue::Pointer(ref v) => v,
            _ => panic!("CompValue not a Pointer")
        }
    }
    fn get_mut<'b>(&self,from: &'b mut CompValue<Ptr,V>)
                   -> &'b mut Self::To where 'a: 'b {
        match from {
            &mut CompValue::Pointer(ref mut v) => v,
            _ => panic!("CompValue not a Pointer")
        }
    }
}

impl<'a,Ptr: 'a,V: 'a> SimplePathEl<'a,CompValue<Ptr,V>> for CompValueVectorP {
    type To = CompVec<CompValue<Ptr,V>>;
    fn get<'b>(&self,from: &'b CompValue<Ptr,V>) -> &'b Self::To where 'a: 'b {
        match from {
            &CompValue::Vector(ref v) => v,
            _ => panic!("CompValue not a Vector")
        }
    }
    fn get_mut<'b>(&self,from: &'b mut CompValue<Ptr,V>)
                   -> &'b mut Self::To where 'a: 'b {
        match from {
            &mut CompValue::Vector(ref mut v) => v,
            _ => panic!("CompValue not a Vector")
        }
    }
}

impl<'a,Em: Embed,Ptr: 'a,V: 'a> PathEl<'a,Em,CompValue<Ptr,V>> for CompValueValueP {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CompValue<Ptr,V>>>(
        &self,
        prev: &Prev,
        from: &PrevFrom,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        prev.read(from,pos,arr,em)
    }
    fn read_slice<'b,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CompValue<Ptr,V>>>(
        &self,
        prev: &Prev,
        from: &PrevFrom,
        pos: usize,
        len: usize,
        arr: &'b [Em::Expr])
        -> Option<&'b [Em::Expr]> {
        prev.read_slice(from,pos,len,arr)
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CompValue<Ptr,V>>>(
        &self,
        prev: &Prev,
        from: &PrevFrom,
        pos: usize,
        e: Em::Expr,
        arr: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        prev.write(from,pos,e,arr,em)
    }
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CompValue<Ptr,V>>>(
        &self,
        prev: &Prev,
        from: &mut PrevFrom,
        pos: usize,
        old_len: usize,
        src: &mut Vec<Em::Expr>,
        trg: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        prev.write_slice(from,pos,old_len,src,trg,em)
    }
}

impl<'a,Em: Embed,Ptr: 'a,V: 'a> PathEl<'a,Em,CompValue<Ptr,V>> for CompValuePointerP {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CompValue<Ptr,V>>>(
        &self,
        prev: &Prev,
        from: &PrevFrom,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        prev.read(from,pos,arr,em)
    }
    fn read_slice<'b,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CompValue<Ptr,V>>>(
        &self,
        prev: &Prev,
        from: &PrevFrom,
        pos: usize,
        len: usize,
        arr: &'b [Em::Expr])
        -> Option<&'b [Em::Expr]> {
        prev.read_slice(from,pos,len,arr)
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CompValue<Ptr,V>>>(
        &self,
        prev: &Prev,
        from: &PrevFrom,
        pos: usize,
        e: Em::Expr,
        arr: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        prev.write(from,pos,e,arr,em)
    }
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CompValue<Ptr,V>>>(
        &self,
        prev: &Prev,
        from: &mut PrevFrom,
        pos: usize,
        old_len: usize,
        src: &mut Vec<Em::Expr>,
        trg: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        prev.write_slice(from,pos,old_len,src,trg,em)
    }
}

impl<'a,Em: Embed,Ptr: 'a,V: 'a> PathEl<'a,Em,CompValue<Ptr,V>> for CompValueVectorP {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CompValue<Ptr,V>>>(
        &self,
        prev: &Prev,
        from: &PrevFrom,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        prev.read(from,pos,arr,em)
    }
    fn read_slice<'b,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CompValue<Ptr,V>>>(
        &self,
        prev: &Prev,
        from: &PrevFrom,
        pos: usize,
        len: usize,
        arr: &'b [Em::Expr])
        -> Option<&'b [Em::Expr]> {
        prev.read_slice(from,pos,len,arr)
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CompValue<Ptr,V>>>(
        &self,
        prev: &Prev,
        from: &PrevFrom,
        pos: usize,
        e: Em::Expr,
        arr: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        prev.write(from,pos,e,arr,em)
    }
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=CompValue<Ptr,V>>>(
        &self,
        prev: &Prev,
        from: &mut PrevFrom,
        pos: usize,
        old_len: usize,
        src: &mut Vec<Em::Expr>,
        trg: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        prev.write_slice(from,pos,old_len,src,trg,em)
    }
}

impl<Ptr: Semantic+HasSorts,V: Semantic> Clone for CompValueMeaning<Ptr,V> {
    fn clone(&self) -> Self {
        match self {
            &CompValueMeaning::Value(ref m) => CompValueMeaning::Value(m.clone()),
            &CompValueMeaning::Pointer(ref p) => CompValueMeaning::Pointer(p.clone()),
            &CompValueMeaning::Vector(ref v) => CompValueMeaning::Vector(v.clone())
        }
    }
}

impl<V: Semantic+HasSorts,U: Semantic> PartialEq for CompValueMeaning<V,U> {
    fn eq(&self,other: &CompValueMeaning<V,U>) -> bool {
        match self {
            &CompValueMeaning::Value(ref p) => match other {
                &CompValueMeaning::Value(ref q) => p.eq(q),
                _ => false
            },
            &CompValueMeaning::Pointer(ref p) => match other {
                &CompValueMeaning::Pointer(ref q) => p.eq(q),
                _ => false
            },
            &CompValueMeaning::Vector(ref p) => match other {
                &CompValueMeaning::Vector(ref q) => p.eq(q),
                _ => false
            }
        }
    }
}

impl<V: Semantic+HasSorts,U: Semantic> Eq for CompValueMeaning<V,U> {}

impl<V: Semantic+HasSorts,U: Semantic> PartialOrd for CompValueMeaning<V,U> {
    fn partial_cmp(&self,other: &CompValueMeaning<V,U>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<V: Semantic+HasSorts,U: Semantic> Ord for CompValueMeaning<V,U> {
    fn cmp(&self,other: &CompValueMeaning<V,U>) -> Ordering {
        match (self,other) {
            (&CompValueMeaning::Value(ref p),
             &CompValueMeaning::Value(ref q)) => p.cmp(q),
            (&CompValueMeaning::Value(_),_) => Ordering::Less,
            (_,&CompValueMeaning::Value(_)) => Ordering::Greater,
            (&CompValueMeaning::Pointer(ref p),
             &CompValueMeaning::Pointer(ref q)) => p.cmp(q),
            (&CompValueMeaning::Pointer(_),_) => Ordering::Less,
            (_,&CompValueMeaning::Pointer(_)) => Ordering::Greater,
            (&CompValueMeaning::Vector(ref p),
             &CompValueMeaning::Vector(ref q)) => p.cmp(q),
        }
    }
}

impl<V: Semantic+HasSorts,U: Semantic> Hash for CompValueMeaning<V,U> {
    fn hash<H>(&self, state: &mut H) where H: Hasher {
        match self {
            &CompValueMeaning::Value(ref p) => {
                (0 as u8).hash(state);
                p.hash(state);
            },
            &CompValueMeaning::Pointer(ref p) => {
                (1 as u8).hash(state);
                p.hash(state);
            },
            &CompValueMeaning::Vector(ref p) => {
                (2 as u8).hash(state);
                p.hash(state);
            }
        }
    }
}

impl<V: Semantic+HasSorts,U: Semantic> fmt::Debug for CompValueMeaning<V,U> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            &CompValueMeaning::Value(ref p) => f.debug_tuple("Value")
                .field(p).finish(),
            &CompValueMeaning::Pointer(ref p) => f.debug_tuple("Pointer")
                .field(p).finish(),
            &CompValueMeaning::Vector(ref p) => f.debug_tuple("Vector")
                .field(p).finish()
        }
    }
}

impl<Ptr: Semantic+HasSorts,V: Semantic+HasSorts> Semantic for CompValue<Ptr,V> {
    type Meaning = CompValueMeaning<Ptr,V>;
    type MeaningCtx = CompValueMeaningCtx<Ptr,V>;
    fn meaning(&self,pos: usize) -> Self::Meaning {
        match self {
            &CompValue::Value(ref v) => CompValueMeaning::Value(v.meaning(pos)),
            &CompValue::Pointer(ref p) => CompValueMeaning::Pointer(p.meaning(pos)),
            &CompValue::Vector(ref v) => CompValueMeaning::Vector(Box::new(v.meaning(pos))),
            &CompValue::Metadata => unreachable!()
        }
    }
    fn fmt_meaning<F : fmt::Write>(&self,m: &Self::Meaning,fmt: &mut F) -> Result<(),fmt::Error> {
        match m {
            &CompValueMeaning::Value(ref nm) => match self {
                &CompValue::Value(ref v) => {
                    write!(fmt,"value.")?;
                    v.fmt_meaning(nm,fmt)
                },
                _ => panic!("Meaning mismatch")
            },
            &CompValueMeaning::Pointer(ref nm) => match self {
                &CompValue::Pointer(ref v) => {
                    write!(fmt,"ptr.")?;
                    v.fmt_meaning(nm,fmt)
                },
                _ => panic!("Meaning mismatch")
            },
            &CompValueMeaning::Vector(ref nm) => match self {
                &CompValue::Vector(ref v) => {
                    write!(fmt,"vec.")?;
                    v.fmt_meaning(nm,fmt)
                },
                _ => panic!("Meaning mismatch")
            }
        }
    }
    fn first_meaning(&self) -> Option<(Self::MeaningCtx,Self::Meaning)> {
        match self {
            &CompValue::Value(ref v) => match v.first_meaning() {
                None => None,
                Some((ctx,m)) => Some((CompValueMeaningCtx::Value(ctx),
                                       CompValueMeaning::Value(m)))
            },
            &CompValue::Pointer(ref p) => match p.first_meaning() {
                None => None,
                Some((ctx,m)) => Some((CompValueMeaningCtx::Pointer(ctx),
                                       CompValueMeaning::Pointer(m)))
            },
            &CompValue::Vector(ref v) => match v.first_meaning() {
                None => None,
                Some((ctx,m)) => Some((CompValueMeaningCtx::Vector(Box::new(ctx)),
                                       CompValueMeaning::Vector(Box::new(m))))
            },
            &CompValue::Metadata => None
        }
    }
    fn next_meaning(&self,ctx: &mut Self::MeaningCtx,
                    m: &mut Self::Meaning) -> bool {
        match self {
            &CompValue::Value(ref v) => match ctx {
                &mut CompValueMeaningCtx::Value(ref mut cctx) => match m {
                    &mut CompValueMeaning::Value(ref mut cm) => v.next_meaning(cctx,cm),
                    _ => unreachable!()
                },
                _ => unreachable!()
            },
            &CompValue::Pointer(ref v) => match ctx {
                &mut CompValueMeaningCtx::Pointer(ref mut cctx) => match m {
                    &mut CompValueMeaning::Pointer(ref mut cm) => v.next_meaning(cctx,cm),
                    _ => unreachable!()
                },
                _ => unreachable!()
            },
            &CompValue::Vector(ref v) => match ctx {
                &mut CompValueMeaningCtx::Vector(ref mut cctx) => match m {
                    &mut CompValueMeaning::Vector(ref mut cm) => v.next_meaning(cctx,cm),
                    _ => unreachable!()
                },
                _ => unreachable!()
            },
            &CompValue::Metadata => unreachable!()
        }
    }
}

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub struct ByteWidth<V> {
    value: V,
    byte_width: usize
}

#[derive(Clone)]
pub struct ByteWidthP;

impl<V> ByteWidth<V> {
    pub fn element() -> ByteWidthP {
        ByteWidthP
    }
}

impl<V: Semantic> Semantic for ByteWidth<V> {
    type Meaning = V::Meaning;
    type MeaningCtx = V::MeaningCtx;
    fn meaning(&self,pos: usize) -> Self::Meaning {
        self.value.meaning(pos)
    }
    fn fmt_meaning<F : fmt::Write>(&self,m: &Self::Meaning,fmt: &mut F)
                                   -> Result<(),fmt::Error> {
        self.value.fmt_meaning(m,fmt)
    }
    fn first_meaning(&self) -> Option<(Self::MeaningCtx,Self::Meaning)> {
        self.value.first_meaning()
    }
    fn next_meaning(&self,ctx: &mut Self::MeaningCtx,
                    m: &mut Self::Meaning) -> bool {
        self.value.next_meaning(ctx,m)
    }
}

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub enum BitVecValue {
    BoolValue(usize),
    BitVecValue(usize)
}

impl BitVecValue {
    pub fn bitwidth(&self) -> usize {
        match self {
            &BitVecValue::BoolValue(w) => w,
            &BitVecValue::BitVecValue(w) => w
        }
    }
    pub fn as_bitvec<'a,Em: Embed,From,P: Path<'a,Em,From,To=Self>>(
        path: &P,
        from: &From,
        arr: &[Em::Expr],
        em: &mut Em
    ) -> Result<Em::Expr,Em::Error> {
        match path.get(from) {
            &BitVecValue::BoolValue(w) => {
                let bit = path.read(from,0,arr,em)?;
                let bv0 = em.const_bitvec(w,BigUint::from(0u8))?;
                let bv1 = em.const_bitvec(w,BigUint::from(1u8))?;
                em.ite(bit,bv0,bv1)
            },
            &BitVecValue::BitVecValue(w) => {
                path.read(from,0,arr,em)
            }
        }
    }
    pub fn bv_op<'a,Em: Embed,
                 FromL,PL: Path<'a,Em,FromL,To=Self>,
                 FromR,PR: Path<'a,Em,FromR,To=Self>,
                 F: FnOnce(Em::Expr,Em::Expr,&mut Em)
                           -> Result<Em::Expr,Em::Error>>(
        lpath: &PL,
        lfrom: &FromL,
        larr:  &[Em::Expr],
        rpath: &PR,
        rfrom: &FromR,
        rarr:  &[Em::Expr],
        res: &mut Vec<Em::Expr>,
        em: &mut Em,
        f: F) -> Result<Self,Em::Error> {

        let szl = lpath.get(lfrom).bitwidth();
        let szr = rpath.get(rfrom).bitwidth();
        assert_eq!(szl,szr);
        let rl = Self::as_bitvec(lpath,lfrom,larr,em)?;
        let rr = Self::as_bitvec(rpath,rfrom,rarr,em)?;
        let outp = f(rl,rr,em)?;
        res.push(outp);
        Ok(BitVecValue::BitVecValue(szl))
    }
    pub fn op<'a,Em: Embed,
              FromL,PL: Path<'a,Em,FromL,To=Self>,
              FromR,PR: Path<'a,Em,FromR,To=Self>,
              FBool: FnOnce(Em::Expr,Em::Expr,&mut Em)
                            -> Result<Em::Expr,Em::Error>,
              FBV: FnOnce(Em::Expr,Em::Expr,&mut Em)
                          -> Result<Em::Expr,Em::Error>>(
        lpath: &PL,
        lfrom: &FromL,
        larr:  &[Em::Expr],
        rpath: &PR,
        rfrom: &FromR,
        rarr:  &[Em::Expr],
        res: &mut Vec<Em::Expr>,
        em: &mut Em,
        fbool: FBool,
        fbv: FBV) -> Result<Self,Em::Error> {

        if let &BitVecValue::BoolValue(szl) = lpath.get(lfrom) {
            if let &BitVecValue::BoolValue(szr) = rpath.get(rfrom) {
                assert_eq!(szl,szr);
                let bitl = lpath.read(lfrom,0,larr,em)?;
                let bitr = rpath.read(rfrom,0,rarr,em)?;
                let outp = fbool(bitl,bitr,em)?;
                res.push(outp);
                return Ok(BitVecValue::BoolValue(szl))
            }
        }
        let szl = lpath.get(lfrom).bitwidth();
        let szr = rpath.get(rfrom).bitwidth();
        assert_eq!(szl,szr);
        let rl = Self::as_bitvec(lpath,lfrom,larr,em)?;
        let rr = Self::as_bitvec(rpath,rfrom,rarr,em)?;
        let outp = fbv(rl,rr,em)?;
        res.push(outp);
        Ok(BitVecValue::BitVecValue(szl))
    }
    pub fn cmp<'a,Em: Embed,
               FromL,PL: Path<'a,Em,FromL,To=Self>,
               FromR,PR: Path<'a,Em,FromR,To=Self>,
               FBool: FnOnce(Em::Expr,Em::Expr,&mut Em)
                             -> Result<Em::Expr,Em::Error>,
               FBV: FnOnce(Em::Expr,Em::Expr,&mut Em)
                           -> Result<Em::Expr,Em::Error>>(
        lpath: &PL,
        lfrom: &FromL,
        larr:  &[Em::Expr],
        rpath: &PR,
        rfrom: &FromR,
        rarr:  &[Em::Expr],
        em: &mut Em,
        fbool: FBool,
        fbv: FBV) -> Result<Em::Expr,Em::Error> {
        if let &BitVecValue::BoolValue(szl) = lpath.get(lfrom) {
            if let &BitVecValue::BoolValue(szr) = rpath.get(rfrom) {
                assert_eq!(szl,szr);
                let bitl = lpath.read(lfrom,0,larr,em)?;
                let bitr = rpath.read(rfrom,0,rarr,em)?;
                let outp = fbool(bitl,bitr,em)?;
                return Ok(outp)
            }
        }
        let szl = lpath.get(lfrom);
        let szr = rpath.get(rfrom);
        assert_eq!(szl,szr);
        let rl = Self::as_bitvec(lpath,lfrom,larr,em)?;
        let rr = Self::as_bitvec(rpath,rfrom,rarr,em)?;
        let outp = fbv(rl,rr,em)?;
        Ok(outp)
    }
    pub fn cmp_bv<'a,Em: Embed,
                  FromL,PL: Path<'a,Em,FromL,To=Self>,
                  FromR,PR: Path<'a,Em,FromR,To=Self>,
                  FBV: FnOnce(Em::Expr,Em::Expr,&mut Em)
                              -> Result<Em::Expr,Em::Error>>(
        lpath: &PL,
        lfrom: &FromL,
        larr:  &[Em::Expr],
        rpath: &PR,
        rfrom: &FromR,
        rarr:  &[Em::Expr],
        em: &mut Em,
        fbv: FBV) -> Result<Em::Expr,Em::Error> {

        let szl = lpath.get(lfrom);
        let szr = rpath.get(rfrom);
        assert_eq!(szl,szr);
        let rl = Self::as_bitvec(lpath,lfrom,larr,em)?;
        let rr = Self::as_bitvec(rpath,rfrom,rarr,em)?;
        let outp = fbv(rl,rr,em)?;
        Ok(outp)
    }
}

impl Semantic for BitVecValue {
    type Meaning = ();
    type MeaningCtx = ();
    fn meaning(&self,pos: usize) -> Self::Meaning {
        ()
    }
    fn fmt_meaning<F : fmt::Write>(&self,_:&Self::Meaning,fmt: &mut F) -> Result<(),fmt::Error> {
        write!(fmt,"#")
    }
    fn first_meaning(&self) -> Option<(Self::MeaningCtx,Self::Meaning)> {
        Some(((),()))
    }
    fn next_meaning(&self,_: &mut Self::MeaningCtx,_: &mut Self::Meaning) -> bool {
        false
    }
}

impl HasSorts for BitVecValue {
    fn num_elem(&self) -> usize { 1 }
    fn elem_sort<Em : Embed>(&self,n:usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        assert_eq!(n,0);
        match *self {
            BitVecValue::BoolValue(_) => em.tp_bool(),
            BitVecValue::BitVecValue(sz) => em.tp_bitvec(sz)
        }
    }
}

impl<'a> Composite<'a> for BitVecValue {
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

        match pl.get(froml) {
            &BitVecValue::BoolValue(sz1) => match pr.get(fromr) {
                &BitVecValue::BoolValue(sz2)
                    => if sz1==sz2 {
                        let bitl = pl.read(froml,0,arrl,em)?;
                        let bitr = pr.read(fromr,0,arrr,em)?;
                        let outp = comb(bitl,bitr,em)?;
                        res.push(outp);
                        Ok(Some(BitVecValue::BoolValue(sz1)))
                    } else {
                        Ok(None)
                    },
                &BitVecValue::BitVecValue(sz2)
                    => if sz1==sz2 {
                        let bitl = pl.read(froml,0,arrl,em)?;
                        let vecr = pr.read(fromr,0,arrr,em)?;
                        let bv0 = em.const_bitvec(sz1,BigUint::from(0u8))?;
                        let bv1 = em.const_bitvec(sz1,BigUint::from(1u8))?;
                        let vecl = em.ite(bitl,bv1,bv0)?;
                        let outp = comb(vecl,vecr,em)?;
                        res.push(outp);
                        Ok(Some(BitVecValue::BitVecValue(sz1)))
                    } else {
                        Ok(None)
                    }
            },
            &BitVecValue::BitVecValue(sz1) => match pr.get(fromr) {
                &BitVecValue::BoolValue(sz2) => if sz1==sz2 {
                    let vecl = pl.read(froml,0,arrl,em)?;
                    let bitr = pr.read(fromr,0,arrr,em)?;
                    let bv0 = em.const_bitvec(sz1,BigUint::from(0u8))?;
                    let bv1 = em.const_bitvec(sz1,BigUint::from(1u8))?;
                    let vecr = em.ite(bitr,bv1,bv0)?;
                    let outp = comb(vecl,vecr,em)?;
                    res.push(outp);
                    Ok(Some(BitVecValue::BitVecValue(sz1)))
                } else {
                    Ok(None)
                },
                &BitVecValue::BitVecValue(sz2) => if sz1==sz2 {
                    let vecl = pl.read(froml,0,arrl,em)?;
                    let vecr = pr.read(fromr,0,arrr,em)?;
                    let outp = comb(vecl,vecr,em)?;
                    res.push(outp);
                    Ok(Some(BitVecValue::BitVecValue(sz1)))
                } else {
                    Ok(None)
                }
            }
        }
    }
}

impl<'a> IntValue<'a> for BitVecValue {
    fn const_int<Em: Embed>(bw: u64,val: BigUint,res: &mut Vec<Em::Expr>,em: &mut Em)
                            -> Result<Self,Em::Error> {
        if bw==1 {
            let el = em.const_bool(val==BigUint::from(1u8))?;
            res.push(el);
            Ok(BitVecValue::BoolValue(1))
        } else {
            let el = em.const_bitvec(bw as usize,val)?;
            Ok(BitVecValue::BitVecValue(bw as usize))
        }
    }
    fn bin<From1,P1: Path<'a,Em,From1,To=Self>,
           From2,P2: Path<'a,Em,From2,To=Self>,
           Em: DeriveValues>(op: &llvm_ir::BinOp,
                             lhs: &P1,
                             lfrom: &From1,
                             larr: &[Em::Expr],
                             rhs: &P2,
                             rfrom: &From2,
                             rarr: &[Em::Expr],
                             res: &mut Vec<Em::Expr>,
                             em: &mut Em)
                             -> Result<Self,Em::Error> {
        match op {
            &llvm_ir::BinOp::Add(_,_)
                => Self::bv_op(lhs,lfrom,larr,
                               rhs,rfrom,rarr,
                               res,em,|x,y,em| em.bvadd(x,y)),
            &llvm_ir::BinOp::Sub(_,_)
                => Self::bv_op(lhs,lfrom,larr,
                               rhs,rfrom,rarr,
                               res,em,|x,y,em| em.bvsub(x,y)),
            &llvm_ir::BinOp::Mul(_,_)
                => Self::bv_op(lhs,lfrom,larr,
                               rhs,rfrom,rarr,
                               res,em,|x,y,em| em.bvmul(x,y)),
            &llvm_ir::BinOp::XOr
                => Self::op(lhs,lfrom,larr,
                            rhs,rfrom,rarr,
                            res,em,
                            |x,y,em| em.xor(vec![x,y]),
                            |x,y,em| em.bvxor(x,y)),
            &llvm_ir::BinOp::AShr
                => Self::bv_op(lhs,lfrom,larr,
                               rhs,rfrom,rarr,
                               res,em,|x,y,em| em.bvashr(x,y)),
            &llvm_ir::BinOp::LShr
                => Self::bv_op(lhs,lfrom,larr,
                               rhs,rfrom,rarr,
                               res,em,|x,y,em| em.bvlshr(x,y)),
            &llvm_ir::BinOp::SDiv(_)
                => Self::bv_op(lhs,lfrom,larr,
                               rhs,rfrom,rarr,
                               res,em,|x,y,em| em.bvsdiv(x,y)),
            &llvm_ir::BinOp::And
                => Self::op(lhs,lfrom,larr,
                            rhs,rfrom,rarr,
                            res,em,
                            |x,y,em| em.and(vec![x,y]),
                            |x,y,em| em.bvand(x,y)),
            &llvm_ir::BinOp::Or
                => Self::op(lhs,lfrom,larr,
                            rhs,rfrom,rarr,
                            res,em,
                            |x,y,em| em.or(vec![x,y]),
                            |x,y,em| em.bvor(x,y)),
            &llvm_ir::BinOp::Shl
                => Self::bv_op(lhs,lfrom,larr,
                               rhs,rfrom,rarr,
                               res,em,|x,y,em| em.bvshl(x,y)),
            _ => panic!("BinOp: {:?}",op)
        }
    }
    fn sext<From,P: Path<'a,Em,From,To=Self>,
            Em: Embed>(path: &P,
                       from: &From,
                       arr: &[Em::Expr],
                       bw: usize,
                       res: &mut Vec<Em::Expr>,
                       em: &mut Em)
                       -> Result<Self,Em::Error> {
        let val = path.read(from,0,arr,em)?;
        match path.get(from) {
            &BitVecValue::BoolValue(sz) => {
                assert!(bw>=sz);
                res.push(val);
                Ok(BitVecValue::BoolValue(bw))
            },
            &BitVecValue::BitVecValue(sz) => {
                assert!(bw>=sz);
                let bv0  = em.const_bitvec(sz,BigUint::from(0u8))?;
                let sign = em.extract(sz-1,1,val.clone())?;
                let rest = em.extract(0,sz-1,val.clone())?;
                let pad0 = em.const_bitvec(bw-sz,BigUint::from(0u8))?;
                let pad1 = em.const_bitvec(bw-sz,BigUint::from(1u8).shl(bw-sz)-1u8)?;
                let pad_cond = em.bvsge(val,bv0)?;
                let pad  = em.ite(pad_cond,pad0,pad1)?;
                let outp1 = em.concat(sign,pad)?;
                let outp2 = em.concat(outp1,rest)?;
                res.push(outp2);
                Ok(BitVecValue::BitVecValue(bw))
            }
        }
    }
    fn zext<From,P: Path<'a,Em,From,To=Self>,
            Em: Embed>(path: &P,
                       from: &From,
                       arr: &[Em::Expr],
                       bw: usize,
                       res: &mut Vec<Em::Expr>,
                       em: &mut Em)
                       -> Result<Self,Em::Error> {
        let val = path.read(from,0,arr,em)?;
        match path.get(from) {
            &BitVecValue::BoolValue(sz) => {
                assert!(bw>=sz);
                res.push(val);
                Ok(BitVecValue::BoolValue(bw))
            },
            &BitVecValue::BitVecValue(sz) => {
                let pad = em.const_bitvec(bw-sz,BigUint::from(0u8))?;
                let outp = em.concat(pad,val)?;
                Ok(BitVecValue::BitVecValue(bw))
            }
        }
    }
    fn trunc<From,P: Path<'a,Em,From,To=Self>,
             Em: Embed>(path: &P,
                        from: &From,
                        arr: &[Em::Expr],
                        bw: usize,
                        res: &mut Vec<Em::Expr>,
                        em: &mut Em)
                        -> Result<Self,Em::Error> {
        let val = path.read(from,0,arr,em)?;
        match path.get(from) {
            &BitVecValue::BoolValue(sz) => {
                assert!(bw<=sz);
                res.push(val);
                Ok(BitVecValue::BoolValue(bw))
            },
            &BitVecValue::BitVecValue(sz) => {
                assert!(bw<=sz);
                let outp = em.extract(0,bw,val)?;
                res.push(outp);
                Ok(BitVecValue::BitVecValue(bw))
            }
        }
    }
    fn icmp<From1,P1: Path<'a,Em,From1,To=Self>,
            From2,P2: Path<'a,Em,From2,To=Self>,
            Em: Embed>(op: &llvm_ir::CmpOp,
                       pl: &P1,froml: &From1,arrl: &[Em::Expr],
                       pr: &P2,fromr: &From2,arrr: &[Em::Expr],
                       em: &mut Em)
                       -> Result<Em::Expr,Em::Error> {
        match op {
            &llvm_ir::CmpOp::Eq => Self::cmp(pl,froml,arrl,
                                             pr,fromr,arrr,
                                             em,
                                             |x,y,em| em.eq(x,y),
                                             |x,y,em| em.eq(x,y)),
            &llvm_ir::CmpOp::Ne => {
                let eq = Self::cmp(pl,froml,arrl,
                                   pr,fromr,arrr,
                                   em,
                                   |x,y,em| em.eq(x,y),
                                   |x,y,em| em.eq(x,y))?;
                em.not(eq)
            },
            &llvm_ir::CmpOp::SGe => Self::cmp_bv(pl,froml,arrl,
                                                 pr,fromr,arrr,
                                                 em,|x,y,em| em.bvsge(x,y)),
            &llvm_ir::CmpOp::SGe => Self::cmp_bv(pl,froml,arrl,
                                                 pr,fromr,arrr,
                                                 em,|x,y,em| em.bvuge(x,y)),
            &llvm_ir::CmpOp::SGt => Self::cmp_bv(pl,froml,arrl,
                                                 pr,fromr,arrr,
                                                 em,|x,y,em| em.bvsgt(x,y)),
            &llvm_ir::CmpOp::UGt => Self::cmp_bv(pl,froml,arrl,
                                                 pr,fromr,arrr,
                                                 em,|x,y,em| em.bvugt(x,y)),
            &llvm_ir::CmpOp::SLt => Self::cmp_bv(pl,froml,arrl,
                                                 pr,fromr,arrr,
                                                 em,|x,y,em| em.bvslt(x,y)),
            &llvm_ir::CmpOp::ULt => Self::cmp_bv(pl,froml,arrl,
                                                 pr,fromr,arrr,
                                                 em,|x,y,em| em.bvult(x,y)),
            _ => panic!("ICmp {:?} not implemented",op)
        }
    }
    fn from_bool<Em: Embed>(e: Em::Expr,
                            res: &mut Vec<Em::Expr>,
                            _: &mut Em)
                            -> Result<Self,Em::Error> {
        res.push(e);
        Ok(BitVecValue::BoolValue(1))
    }
    fn to_bool<From,P: Path<'a,Em,From,To=Self>,
               Em: Embed>(path: &P,
                          from: &From,
                          arr: &[Em::Expr],
                          em: &mut Em)
                          -> Result<Em::Expr,Em::Error> {
        let val = path.read(from,0,arr,em)?;
        match path.get(from) {
            &BitVecValue::BoolValue(_) => Ok(val),
            &BitVecValue::BitVecValue(bw) => {
                let zero = em.const_bitvec(bw,BigUint::from(0u8))?;
                let eq = em.eq(val,zero)?;
                em.not(eq)
            }
        }
    }
    fn to_offset<From,P: Path<'a,Em,From,To=Self>,
                 Em: Embed>(path: &P,
                            from: &From,
                            arr: &[Em::Expr],
                            res: &mut Vec<Em::Expr>,
                            em: &mut Em)
                            -> Result<Singleton,Em::Error> {
        let w = path.get(from).bitwidth();
        let val = Self::as_bitvec(path,from,arr,em)?;
        res.push(val);
        Ok(Singleton(Sort::from_kind(SortKind::BitVec(w))))
    }
    fn from_offset<From,P: Path<'a,Em,From,To=Singleton>,
                   Em: Embed>(bw: usize,
                              path: &P,
                              from: &From,
                              arr: &[Em::Expr],
                              res: &mut Vec<Em::Expr>,
                              em: &mut Em)
                              -> Result<Self,Em::Error> {
        let val = path.read(from,0,arr,em)?;
        match path.get(from).0.kind() {
            SortKind::Bool => {
                res.push(val);
                Ok(BitVecValue::BoolValue(bw))
            },
            SortKind::BitVec(w) => {
                assert_eq!(w,bw);
                res.push(val);
                Ok(BitVecValue::BitVecValue(bw))
            },
            _ => unimplemented!()
        }
    }
}

impl<'a> Bytes<'a> for BitVecValue {
    fn byte_width(&self) -> usize {
        match self {
            &BitVecValue::BoolValue(sz) => sz/8,
            &BitVecValue::BitVecValue(sz) => sz/8
        }
    }
    fn extract_bytes<Em: Embed,From,P: Path<'a,Em,From,To=Self>>(
        path: &P,from: &From,arr: &[Em::Expr],
        start: usize,len: usize,
        res: &mut Vec<Em::Expr>,
        em: &mut Em
    ) -> Result<Option<Self>,Em::Error> {
        match path.get(from) {
            &BitVecValue::BoolValue(sz) => {
                let rsz = sz/8;
                if start+len==rsz {
                    let val = path.read(from,0,arr,em)?;
                    res.push(val);
                } else {
                    let outp = em.const_bool(false)?;
                    res.push(outp);
                }
                Ok(Some(BitVecValue::BoolValue(len*8)))
            },
            &BitVecValue::BitVecValue(_) => {
                //let rsz = sz/8;
                unimplemented!()
                //let ninp = Transformation::map_by_elem(Box::new(|_,_,e,em| { em.
            }
        }
    }
}

impl<Ptr: HasSorts,V: HasSorts> HasSorts for CompValue<Ptr,V> {
    fn num_elem(&self) -> usize {
        match self {
            &CompValue::Value(ref v) => v.num_elem(),
            &CompValue::Pointer(ref p) => p.num_elem(),
            &CompValue::Vector(ref v) => v.num_elem(),
            &CompValue::Metadata => 0
        }
    }
    fn elem_sort<Em : Embed>(&self,n:usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        match self {
            &CompValue::Value(ref v) => v.elem_sort(n,em),
            &CompValue::Pointer(ref p) => p.elem_sort(n,em),
            &CompValue::Vector(ref v) => v.elem_sort(n,em),
            &CompValue::Metadata => unreachable!()
        }
    }
}

impl<'a,Ptr: Composite<'a>+Clone,V: Composite<'a>+Clone
     > Composite<'a> for CompValue<Ptr,V> {
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

        match pl.get(froml) {
            &CompValue::Value(ref vx) => {
                let rvy = match pr.get(fromr) {
                    &CompValue::Value(ref vy) => vy,
                    _ => return Ok(None)
                };
                match V::combine(&pl.clone().then(Self::value()),froml,arrl,
                                 &pr.clone().then(Self::value()),fromr,arrr,
                                 comb,only_l,only_r,res,em)? {
                    None => Ok(None),
                    Some(nv) => Ok(Some(CompValue::Value(nv)))
                }
            },
            &CompValue::Pointer(ref vx) => {
                let rvy = match pr.get(fromr) {
                    &CompValue::Pointer(ref vy) => vy,
                    _ => return Ok(None)
                };
                match BitField::combine(&pl.clone().then(Self::pointer()),froml,arrl,
                                        &pr.clone().then(Self::pointer()),fromr,arrr,
                                        comb,only_l,only_r,res,em)? {
                    None => Ok(None),
                    Some(nv) => Ok(Some(CompValue::Pointer(nv)))
                }
            },
            &CompValue::Vector(ref vx) => {
                let rvy = match pr.get(fromr) {
                    &CompValue::Vector(ref vy) => vy,
                    _ => return Ok(None)
                };
                match CompVec::combine(&pl.clone().then(Self::vector()),froml,arrl,
                                       &pr.clone().then(Self::vector()),fromr,arrr,
                                       comb,only_l,only_r,res,em)? {
                    None => Ok(None),
                    Some(nv) => Ok(Some(CompValue::Vector(nv)))
                }
            },
            &CompValue::Metadata => {
                match pr.get(fromr) {
                    &CompValue::Metadata => Ok(Some(CompValue::Metadata)),
                    _ => Ok(None)
                }
            }
        }
    }
}

impl<'a,Ptr: Composite<'a>,V: Composite<'a>> FromMD<'a> for CompValue<Ptr,V> {
    fn from_md<Em: Embed>(_: &'a llvm_ir::Metadata,
                          _: &mut Vec<Em::Expr>,
                          _: &mut Em)
                          -> Result<Self,Em::Error> {
        Ok(CompValue::Metadata)
    }
}

impl<'a,Ptr: Pointer<'a>+Bytes<'a>+Clone,V: 'a+IntValue<'a>+Bytes<'a>+Clone> IntValue<'a> for CompValue<Ptr,V> {
    fn to_offset<From,P: Path<'a,Em,From,To=Self>,
                 Em: Embed>(path: &P,from: &From,inp: &[Em::Expr],
                            res: &mut Vec<Em::Expr>,em: &mut Em)
                            -> Result<Singleton,Em::Error> {
        V::to_offset(&then(path.clone(),CompValueValueP),from,inp,res,em)
    }
    fn from_offset<From,P: Path<'a,Em,From,To=Singleton>,
                   Em: Embed>(bw: usize,
                              path: &P,
                              from: &From,
                              arr: &[Em::Expr],
                              res: &mut Vec<Em::Expr>,
                              em: &mut Em)
                              -> Result<Self,Em::Error> {
        let v = V::from_offset(bw,path,from,arr,res,em)?;
        Ok(CompValue::Value(v))
    }
    fn const_int<Em: Embed>(bw: u64,val: BigUint,res: &mut Vec<Em::Expr>,em: &mut Em)
                            -> Result<Self,Em::Error> {
        let v = V::const_int(bw,val,res,em)?;
        Ok(CompValue::Value(v))
    }
    fn bin<From1,P1: Path<'a,Em,From1,To=Self>,
           From2,P2: Path<'a,Em,From2,To=Self>,
           Em: DeriveValues>(op: &llvm_ir::BinOp,
                             lhs: &P1,
                             lfrom: &From1,
                             larr: &[Em::Expr],
                             rhs: &P2,
                             rfrom: &From2,
                             rarr: &[Em::Expr],
                             res: &mut Vec<Em::Expr>,
                             em: &mut Em)
                             -> Result<Self,Em::Error> {
        match lhs.get(lfrom) {
            &CompValue::Value(_) => {
                let nv = V::bin(op,
                                &then(lhs.clone(),CompValueValueP),lfrom,larr,
                                &then(rhs.clone(),CompValueValueP),rfrom,rarr,
                                res,em)?;
                Ok(CompValue::Value(nv))
            },
            &CompValue::Pointer(_) => match op {
                &llvm_ir::BinOp::And => match rhs.get(rfrom) {
                    &CompValue::Value(_) => {
                        let mut mask_inp = Vec::new();
                        let mask = V::to_offset(&then(rhs.clone(),CompValueValueP),rfrom,rarr,
                                                &mut mask_inp,em)?;
                        let val = Singleton::get(&Id,&mask,&mask_inp[..],em)?;
                        match em.derive_const(&val)? {
                            None => unimplemented!(),
                            Some(mask_c) => if value_as_index(&mask_c)<8 {
                                let nv = V::const_int((rhs.get(rfrom).byte_width()*8) as u64,
                                                      BigUint::from(0u8),res,em)?;
                                Ok(CompValue::Value(nv))
                            } else {
                                unimplemented!()
                            }
                        }
                    },
                    _ => unimplemented!()
                },
                &llvm_ir::BinOp::Sub(_,_) => match rhs.get(rfrom) {
                    &CompValue::Pointer(ref rrhs) => {
                        let bw = lhs.get(lfrom).byte_width()*8;
                        let mut l_base_inp = Vec::new();
                        let l_base = BitField::to_pointer(&then(lhs.clone(),CompValuePointerP),lfrom,larr,
                                                          &mut l_base_inp,em)?.unwrap();
                        let mut r_base_inp = Vec::new();
                        let r_base = BitField::to_pointer(&then(rhs.clone(),CompValuePointerP),rfrom,rarr,
                                                          &mut r_base_inp,em)?.unwrap();
                        let tp: SortKind<Sort> = SortKind::BitVec(bw);
                        let sub = ptr_sub(&Id,&l_base,&l_base_inp[..],
                                          &Id,&r_base,&r_base_inp[..],&tp,em)?;
                        let srt = Singleton(Sort::from_kind(tp));
                        let ret = V::from_offset(bw,&Id,&srt,&[sub],res,em)?;
                        Ok(CompValue::Value(ret))
                    },
                    _ => unimplemented!()
                },
                _ => unimplemented!()
            },
            _ => unimplemented!()
        }
    }
    fn sext<From,P: Path<'a,Em,From,To=Self>,
            Em: Embed>(path: &P,from: &From,inp: &[Em::Expr],
                       sz: usize,res: &mut Vec<Em::Expr>,em: &mut Em)
                       -> Result<Self,Em::Error>
    where Self: 'a {
        match path.get(from) {
            &CompValue::Value(_) => {
                let nv = V::sext(&then(path.clone(),CompValueValueP),from,inp,sz,res,em)?;
                Ok(CompValue::Value(nv))
            },
            _ => unimplemented!()
        }
    }
    fn zext<From,P: Path<'a,Em,From,To=Self>,
            Em: Embed>(path: &P,from: &From,inp: &[Em::Expr],
                       sz: usize,res: &mut Vec<Em::Expr>,em: &mut Em)
                       -> Result<Self,Em::Error>
    where Self: 'a {
        match path.get(from) {
            &CompValue::Value(_) => {
                let nv = V::zext(&then(path.clone(),CompValueValueP),from,inp,sz,res,em)?;
                Ok(CompValue::Value(nv))
            },
            _ => unimplemented!()
        }
    }
    fn trunc<From,P: Path<'a,Em,From,To=Self>,
             Em: Embed>(path: &P,from: &From,inp: &[Em::Expr],
                        sz: usize,res: &mut Vec<Em::Expr>,em: &mut Em)
                        -> Result<Self,Em::Error>
    where Self: 'a {
        match path.get(from) {
            &CompValue::Value(_) => {
                let nv = V::trunc(&then(path.clone(),CompValueValueP),from,inp,sz,res,em)?;
                Ok(CompValue::Value(nv))
            },
            _ => unimplemented!()
        }
    }
    fn icmp<From1,P1: Path<'a,Em,From1,To=Self>,
            From2,P2: Path<'a,Em,From2,To=Self>,
            Em: Embed>(op: &llvm_ir::CmpOp,
                       p1: &P1,from1: &From1,inp1: &[Em::Expr],
                       p2: &P2,from2: &From2,inp2: &[Em::Expr],
                       em: &mut Em)
                       -> Result<Em::Expr,Em::Error>
    where Self: 'a {

        match p1.get(from1) {
            &CompValue::Value(_) => match p2.get(from2) {
                &CompValue::Value(_) => V::icmp(op,
                                                &then(p1.clone(),
                                                      CompValueValueP),
                                                from1,inp1,
                                                &then(p2.clone(),
                                                      CompValueValueP),
                                                from2,inp2,em),
                _ => unimplemented!()
            },
            &CompValue::Pointer(_) => match p2.get(from2) {
                &CompValue::Pointer(_) => match op {
                    &llvm_ir::CmpOp::Eq => BitField::ptr_eq(&then(p1.clone(),
                                                                  CompValuePointerP),
                                                            from1,inp1,
                                                            &then(p2.clone(),
                                                                  CompValuePointerP),
                                                            from2,inp2,em),
                    &llvm_ir::CmpOp::Ne => {
                        let x = BitField::ptr_eq(&then(p1.clone(),
                                                       CompValuePointerP),
                                                 from1,inp1,
                                                 &then(p2.clone(),
                                                       CompValuePointerP),
                                                 from2,inp2,em)?;
                        em.not(x)
                    },
                    &llvm_ir::CmpOp::ULt => BitField::ptr_lt(&then(p1.clone(),
                                                                   CompValuePointerP),
                                                             from1,inp1,
                                                             &then(p2.clone(),
                                                                   CompValuePointerP),
                                                             from2,inp2,em),
                    _ => unimplemented!()
                },
                _ => unimplemented!()
            },
            _ => unimplemented!()
        }
    }
    fn from_bool<Em: Embed>(e: Em::Expr,res: &mut Vec<Em::Expr>,em: &mut Em)
                            -> Result<Self,Em::Error> {
        let r = V::from_bool(e,res,em)?;
        Ok(CompValue::Value(r))
    }
    fn to_bool<From,P: Path<'a,Em,From,To=Self>,
               Em: Embed>(path: &P,from: &From,inp: &[Em::Expr],em: &mut Em)
                          -> Result<Em::Expr,Em::Error>
    where Self: 'a {
        match path.get(from) {
            &CompValue::Value(_) => V::to_bool(&then(path.clone(),CompValueValueP),from,inp,em),
            _ => unimplemented!()
        }
    }
}

impl<'a,Ptr: 'a+Bytes<'a>+Clone,V: 'a+Bytes<'a>+Clone> Bytes<'a> for CompValue<Ptr,V> {
    fn byte_width(&self) -> usize {
        match self {
            &CompValue::Value(ref v) => v.byte_width(),
            &CompValue::Pointer(ref p) => p.obj.byte_width(),
            &CompValue::Vector(_) => {
                let vec_path = then(Id,CompValueVectorP);
                let els = CompVec::elements(vec_path,self);
                let mut acc = 0;
                for el in els {
                    acc+=el.get(self).byte_width();
                }
                acc
            },
            &CompValue::Metadata => unimplemented!()
        }
    }
    fn extract_bytes<Em: Embed,From,P: Path<'a,Em,From,To=Self>>(
        path: &P,from: &From,arr: &[Em::Expr],
        start: usize,len: usize,
        res: &mut Vec<Em::Expr>,
        em: &mut Em
    ) -> Result<Option<Self>,Em::Error> {
        match path.get(from) {
            &CompValue::Value(_) => {
                match V::extract_bytes(&then(path.clone(),CompValueValueP),
                                       from,arr,start,len,res,em)? {
                    None => Ok(None),
                    Some(nv) => Ok(Some(CompValue::Value(nv)))
                }
            },
            &CompValue::Pointer(_) => {
                match BitField::extract_bytes(&then(path.clone(),CompValuePointerP),
                                              from,arr,start,len,res,em)? {
                    None => Ok(None),
                    Some(nv) => Ok(Some(CompValue::Pointer(nv)))
                }
            },
            &CompValue::Vector(_) => {
                let vec_path = then(path.clone(),CompValueVectorP);
                let els = CompVec::elements(vec_path,from);
                let mut acc = 0;
                for el in els {
                    let sz = el.get(from).byte_width();
                    if start >= acc {
                        if len + start - acc > sz {
                            return Ok(None)
                        } else {
                            return CompValue::extract_bytes(&el,from,arr,
                                                            start-acc,len,res,em)
                        }
                    }
                    acc+=sz;
                }
                Ok(None)
            },
            _ => unimplemented!()
        }
    }
}

impl<'a,Ptr: Pointer<'a>+Clone,V: 'a+Composite<'a>+Clone> Pointer<'a> for CompValue<Ptr,V> {
    fn from_pointer<Em: Embed,From,P: Path<'a,Em,From,To=BasePointer<'a>>>(
        bw: usize,
        path: &P,
        from: &From,
        inp: &[Em::Expr],
        res: &mut Vec<Em::Expr>,
        em: &mut Em
    ) -> Result<Self,Em::Error> {
        let nptr = BitField::from_pointer(bw,path,from,inp,res,em)?;
        Ok(CompValue::Pointer(nptr))
    }
    fn to_pointer<Em: Embed,From,P: Path<'a,Em,From,To=Self>>(
        path: &P,
        from: &From,
        inp:  &[Em::Expr],
        res:  &mut Vec<Em::Expr>,
        em:   &mut Em
    ) -> Result<Option<BasePointer<'a>>,Em::Error> {
        match path.get(from) {
            &CompValue::Pointer(_) => {
                let ptr = then(path.clone(),
                               CompValuePointerP);
                BitField::to_pointer(&ptr,from,inp,res,em)
            },
            _ => unimplemented!()
        }
    }
    fn ptr_eq<Em: Embed,
              From1,P1: Path<'a,Em,From1,To=Self>,
              From2,P2: Path<'a,Em,From2,To=Self>>(
        p1: &P1,from1: &From1,inp1: &[Em::Expr],
        p2: &P2,from2: &From2,inp2: &[Em::Expr],
        em: &mut Em
    ) -> Result<Em::Expr,Em::Error> {
        match p1.get(from1) {
            &CompValue::Pointer(_) => match p2.get(from2) {
                &CompValue::Pointer(_) => {
                    let ptr1 = then(p1.clone(),CompValuePointerP);
                    let ptr2 = then(p2.clone(),CompValuePointerP);
                    BitField::ptr_eq(&ptr1,from1,inp1,
                                     &ptr2,from2,inp2,em)
                },
                _ => unimplemented!()
            },
            _ => unimplemented!()
        }
    }
    fn ptr_lt<Em: Embed,
              From1,P1: Path<'a,Em,From1,To=Self>,
              From2,P2: Path<'a,Em,From2,To=Self>>(
        p1: &P1,from1: &From1,inp1: &[Em::Expr],
        p2: &P2,from2: &From2,inp2: &[Em::Expr],
        em: &mut Em
    ) -> Result<Em::Expr,Em::Error> {
        match p1.get(from1) {
            &CompValue::Pointer(_) => match p2.get(from2) {
                &CompValue::Pointer(_) => {
                    let ptr1 = then(p1.clone(),CompValuePointerP);
                    let ptr2 = then(p2.clone(),CompValuePointerP);
                    BitField::ptr_lt(&ptr1,from1,inp1,
                                     &ptr2,from2,inp2,em)
                },
                _ => unimplemented!()
            },
            _ => unimplemented!()
        }
    }
}

impl<'a,C: 'a> SimplePathEl<'a,ByteWidth<C>> for ByteWidthP {
    type To = C;
    fn get<'b>(&self,from: &'b ByteWidth<C>) -> &'b Self::To where 'a: 'b {
        &from.value
    }
    fn get_mut<'b>(&self,from: &'b mut ByteWidth<C>) -> &'b mut Self::To where 'a: 'b {
        &mut from.value
    }
}

impl<'a,Em: Embed,C: 'a> PathEl<'a,Em,ByteWidth<C>> for ByteWidthP {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=ByteWidth<C>>>(
        &self,
        prev: &Prev,
        from: &PrevFrom,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        prev.read(from,pos,arr,em)
    }
    fn read_slice<'b,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=ByteWidth<C>>>(
        &self,
        prev: &Prev,
        from: &PrevFrom,
        pos: usize,
        len: usize,
        arr: &'b [Em::Expr])
        -> Option<&'b [Em::Expr]> {
        prev.read_slice(from,pos,len,arr)
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=ByteWidth<C>>>(
        &self,
        prev: &Prev,
        from: &PrevFrom,
        pos: usize,
        e: Em::Expr,
        arr: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        prev.write(from,pos,e,arr,em)
    }
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=ByteWidth<C>>>(
        &self,
        prev: &Prev,
        from: &mut PrevFrom,
        pos: usize,
        old_len: usize,
        src: &mut Vec<Em::Expr>,
        trg: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {
        prev.write_slice(from,pos,old_len,src,trg,em)
    }
}

impl<C: HasSorts> HasSorts for ByteWidth<C> {
    fn num_elem(&self) -> usize {
        self.value.num_elem()
    }
    fn elem_sort<Em: Embed>(&self,n:usize,em: &mut Em)
                            -> Result<Em::Sort,Em::Error> {
        self.value.elem_sort(n,em)
    }
}

impl<'a,C: Composite<'a>> Composite<'a> for ByteWidth<C> {
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

        let w = pl.get(froml).byte_width;
        if w!=pr.get(fromr).byte_width {
            return Ok(None)
        }
        match C::combine(&pl.clone().then(Self::element()),froml,arrl,
                         &pr.clone().then(Self::element()),fromr,arrr,
                         comb,only_l,only_r,res,em)? {
            None => Ok(None),
            Some(nv) => {
                Ok(Some(ByteWidth { value: nv,
                                    byte_width: w }))
            }
        }
    }
}

impl<'a,C: Pointer<'a>+Clone> Pointer<'a> for ByteWidth<C> {
    fn from_pointer<Em: Embed,From,P: Path<'a,Em,From,To=BasePointer<'a>>>(
        bw:   usize,
        path: &P,
        from: &From,
        inp:  &[Em::Expr],
        res:  &mut Vec<Em::Expr>,
        em:   &mut Em
    ) -> Result<Self,Em::Error> {
        let val = C::from_pointer(bw,path,from,inp,res,em)?;
        Ok(ByteWidth { value: val,
                       byte_width: bw })
    }
    fn to_pointer<Em: Embed,From,P: Path<'a,Em,From,To=Self>>(
        path: &P,
        from: &From,
        inp:  &[Em::Expr],
        res:  &mut Vec<Em::Expr>,
        em:   &mut Em
    ) -> Result<Option<BasePointer<'a>>,Em::Error> {
        let el = then(path.clone(),
                      ByteWidthP);
        C::to_pointer(&el,from,inp,res,em)
    }
    fn ptr_eq<Em: Embed,
              From1,P1: Path<'a,Em,From1,To=Self>,
              From2,P2: Path<'a,Em,From2,To=Self>>(
        p1: &P1,from1: &From1,inp1: &[Em::Expr],
        p2: &P2,from2: &From2,inp2: &[Em::Expr],
        em: &mut Em
    ) -> Result<Em::Expr,Em::Error> {
        let el1 = then(p1.clone(),ByteWidthP);
        let el2 = then(p2.clone(),ByteWidthP);
        C::ptr_eq(&el1,from1,inp1,
                  &el2,from2,inp2,em)
    }
    fn ptr_lt<Em: Embed,
              From1,P1: Path<'a,Em,From1,To=Self>,
              From2,P2: Path<'a,Em,From2,To=Self>>(
        p1: &P1,from1: &From1,inp1: &[Em::Expr],
        p2: &P2,from2: &From2,inp2: &[Em::Expr],
        em: &mut Em
    ) -> Result<Em::Expr,Em::Error> {
        let el1 = then(p1.clone(),ByteWidthP);
        let el2 = then(p2.clone(),ByteWidthP);
        C::ptr_lt(&el1,from1,inp1,
                  &el2,from2,inp2,em)
    }
}

impl<'a,C: 'a+Composite<'a>+Clone> Bytes<'a> for ByteWidth<C> {
    fn byte_width(&self) -> usize {
        self.byte_width
    }
    fn extract_bytes<Em: Embed,From,P: Path<'a,Em,From,To=Self>>(
        path: &P,from: &From,arr: &[Em::Expr],
        start: usize,len: usize,
        res: &mut Vec<Em::Expr>,
        em: &mut Em
    ) -> Result<Option<Self>,Em::Error> {
        Ok(None)
    }
}

impl<'a,Ptr: Composite<'a>+Clone,V: Composite<'a>+Clone> Vector<'a> for CompValue<Ptr,V> {
    fn vector<Em: Embed>(vec: Vec<Self>,
                         inp_vec: &mut Vec<Em::Expr>,
                         _: &mut Em)
                         -> Result<Self,Em::Error> {
        Ok(CompValue::Vector(CompVec::from_vec(vec)))
    }
}

impl<'a,Ptr: 'a+Bytes<'a>+Pointer<'a>+Clone,
     V: 'a+Bytes<'a>+IntValue<'a>+Clone> FromConst<'a> for CompValue<Ptr,V> {
    fn from_const<'b,Em : Embed>(dl: &'a DataLayout,
                                 c: &'a llvm_ir::Constant,
                                 tp: &'a Type,
                                 tps: &'a HashMap<String,Type>,
                                 res: &mut Vec<Em::Expr>,
                                 em: &mut Em)
                                 -> Result<Option<Self>,Em::Error> {
        let ret = translate_constant(dl,c,tp,tps,res,em)?;
        Ok(Some(ret))
    }
}

fn value_as_index(val: &Value) -> usize {
    match val {
        &Value::Int(ref v) => v.to_usize().unwrap(),
        &Value::BitVec(_,ref v) => v.to_usize().unwrap(),
        _ => panic!("Value not an index")
    }
}
