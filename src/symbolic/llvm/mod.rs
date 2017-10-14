extern crate smtrs;
extern crate num_bigint;
extern crate num_traits;
extern crate llvm_ir;

pub mod mem;
pub mod frame;
pub mod thread;
pub mod program;
pub mod error;
pub mod pointer;
pub mod library;

use self::smtrs::composite::*;
use self::smtrs::embed::{Embed,DeriveConst,DeriveValues};
use self::smtrs::types::{Sort,SortKind,Value};
use self::num_bigint::BigUint;
use self::num_traits::cast::ToPrimitive;
use std::ops::Shl;
use std::fmt::Debug;
use std::collections::HashMap;
use self::mem::{Bytes,FromConst,MemSlice,MemObj};
use self::frame::*;
use self::thread::*;
use self::program::*;
use self::pointer::*;
use self::library::Library;
use self::llvm_ir::Module;
use self::llvm_ir::datalayout::{DataLayout};
use self::llvm_ir::types::{Type};
use std::iter::{Once,once};
use std::cmp::Ordering;
use std::hash::{Hash,Hasher};
use std::fmt;

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash,Copy,Clone,Debug)]
pub struct InstructionRef<'a> {
    pub function: &'a String,
    pub basic_block: &'a String,
    pub instruction: usize
}

pub enum TrErr<'a,V : Bytes + Clone,Err> {
    EmErr(Err),
    InputNeeded(ProgramInput<'a,V>)
}

impl<'a,V : Bytes+Clone,Err> From<Err> for TrErr<'a,V,Err> {
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

pub fn translate_init<'a,'b,V,Em>(module: &'a Module,
                                  entry_fun: &'a String,
                                  args: Vec<V>,
                                  inp_args: Transf<Em>,
                                  aux: Vec<Vec<u8>>,
                                  em: &mut Em)
                                  -> Result<(OptRef<'b,Program<'a,V>>,Transf<Em>),Em::Error>
    where V : Bytes+FromConst<'a>+Clone, Em : Embed {

    let main_fun = module.functions.get(entry_fun).expect("Entry function not found in module");
    let main_blk = match main_fun.body {
        None => panic!("Entry function has no body"),
        Some(ref bbs) => if bbs.len()==0 {
            panic!("Entry function has no basic blocks")
        } else {
            &bbs[0].name
        }
    };
    
    let (values_main,inp_values_main) = assoc_empty()?;
    let (act_main0,inp_act_main0) = choice_empty();
    let (act_main,inp_act_main) = choice_insert(OptRef::Owned(act_main0),inp_act_main0,
                                                Transformation::const_bool(true,em)?,
                                                OptRef::Owned(Data(InstructionRef { function: entry_fun,
                                                                                    basic_block: main_blk,
                                                                                    instruction: 0 })),
                                                Transformation::id(0))?;
    let (phi_main,inp_phi_main) = choice_empty();

    let (cf_main,inp_cf_main) = call_frame(values_main,inp_values_main,
                                           OptRef::Owned(args),inp_args,
                                           act_main,inp_act_main,
                                           OptRef::Owned(phi_main),inp_phi_main);
    let (prev_main0,inp_prev_main0) = choice_empty();
    let (prev_main,inp_prev_main) = choice_insert(OptRef::Owned(prev_main0),inp_prev_main0,
                                                  Transformation::const_bool(true,em)?,
                                                  OptRef::Owned(Data(None)),
                                                  Transformation::id(0))?;
    let (alloc_main,inp_alloc_main) = assoc_empty()?;
    let (fr_main,inp_fr_main) = frame(prev_main,inp_prev_main,alloc_main,inp_alloc_main);

    let (cs_el,inp_cs_el) = tuple(cf_main,fr_main,inp_cf_main,inp_fr_main);
    
    let (css,inp_css) = bv_vec_stack_singleton(INDEX_WIDTH,cs_el,inp_cs_el,em)?;
    let (cs_main0,inp_cs_main0) = assoc_empty()?;
    let (cs_main,inp_cs_main) = assoc_insert(cs_main0,inp_cs_main0,
                                             &(None,entry_fun),
                                             css,inp_css)?;
    let (st_main,inp_st_main) = assoc_empty()?;
    let (top_main0,inp_top_main0) = choice_empty();
    let (top_main,inp_top_main) = choice_insert(OptRef::Owned(top_main0),inp_top_main0,
                                                Transformation::const_bool(true,em)?,
                                                OptRef::Owned(Data(Some(ContextId::Call((None,entry_fun))))),
                                                Transformation::id(0))?;
    let ret = OptRef::Owned(None);
    let inp_ret = Transformation::id(0);

    let (thread_main,inp_thread_main) = thread(cs_main,inp_cs_main,
                                               st_main,inp_st_main,
                                               top_main,inp_top_main,
                                               ret,inp_ret);

    let thread_pool = OptRef::Owned(vec![thread_main.as_obj()]);
    let inp_thread_pool = inp_thread_main;
    
    let (threads0,inp_threads0) = assoc_empty()?;
    let (threads,inp_threads) = assoc_insert(threads0,inp_threads0,
                                             &(None,entry_fun),
                                             thread_pool,inp_thread_pool)?;

    let (globals0,inp_globals0) = assoc_empty()?;
    let mut globals = globals0;
    let mut inp_globals = inp_globals0;

    for (name,glob) in module.globals.iter() {
        let obj = match glob.initialization {
            None => {
                let sz = module.datalayout.type_size_in_bits(&glob.types,&module.types);
                MemSlice(vec![MemObj::FreshObj(sz as usize)])
            },
            Some(ref init) => translate_global(&module.datalayout,
                                               init,
                                               &glob.types,
                                               &module.types)
        };
        let (nglobals,inp_nglobals) = assoc_insert(globals,
                                                   inp_globals,
                                                   &name,
                                                   OptRef::Owned(obj),
                                                   Transformation::id(0))?;
        globals = nglobals;
        inp_globals = inp_nglobals;
    }

    let (heap,inp_heap) = assoc_empty()?;
    
    Ok(program(threads,inp_threads,globals,inp_globals,heap,inp_heap,OptRef::Owned(aux)))
}

fn filter_ctx_id<'a,V>(cf_id: &CallId<'a>,el: (ThreadView<'a,V>,&Data<Option<ContextId<'a>>>))
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
}

fn update_activation<'a,Em : Embed,V : ViewMut<Element=Activation<'a>>>(
    view: &V,
    viewed: &mut V::Viewed,
    conds: &Vec<Transf<Em>>,
    instr_id: InstructionRef<'a>,
    updates: &mut Updates<Em>,
    orig_inp: Transf<Em>,
    em: &mut Em
) -> Result<(),Em::Error> {

    let (nacts,nacts_inp) = {
        let (acts,acts_inp) = if conds.len()==0 {
            let (r,inp) = choice_empty();
            (OptRef::Owned(r),inp)
        } else {
            let (r,inp) = view.get_with_upd(viewed,updates,orig_inp);
            (OptRef::Ref(r),inp)
        };
        let rcond = if conds.len()==0 {
            let c = em.const_bool(true)?;
            Transformation::constant(vec![c])
        } else {
            Transformation::and(conds.clone())
        };
        let (nacts,nacts_inp) = choice_set_chosen(acts,acts_inp,rcond,
                                                  OptRef::Owned(Data(instr_id)),
                                                  Transformation::id(0))?;
        (nacts.as_obj(),nacts_inp)
    };
    view.write(nacts,nacts_inp,viewed,updates);
    Ok(())
}

pub trait TranslationCfg<Em : Embed> {
    fn change_thread_activation(
        &mut self,
        _:&mut Vec<Transf<Em>>,_:usize,_:&mut Em)
        -> Result<(),Em::Error> {
        Ok(())
    }
    fn change_context_activation(
        &mut self,
        _:&mut Vec<Transf<Em>>,_:usize,_:&mut Em)
        -> Result<(),Em::Error> {
        Ok(())
    }
    fn change_call_frame_activation(
        &mut self,
        _:&mut Vec<Transf<Em>>,_:usize,_:&mut Em)
        -> Result<(),Em::Error> {
        Ok(())
    }
    fn change_instr_activation(
        &mut self,
        _:&mut Vec<Transf<Em>>,_:usize,_:&mut Em)
        -> Result<(),Em::Error> {
        Ok(())
    }
}

pub struct DefaultCfg {}

impl<Em : Embed> TranslationCfg<Em> for DefaultCfg {}

fn eval_phi<'b,ValsView,V,Em>(m: &'b Module,
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
    where ValsView : ViewMut<Viewed=Program<'b,V>,Element=Assoc<&'b String,V>>+Clone,
          V : 'b+Bytes+FromConst<'b>+IntValue+Vector+Pointer<'b>+Debug,
          Em : DeriveValues {
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
}

pub fn translate_instr<'b,V,Cfg,Lib,Em>(
    m: &'b Module,
    cfg: &mut Cfg,
    lib: &Lib,
    thread_id: ThreadId<'b>,
    cf_id: CallId<'b>,
    instr_id: InstructionRef<'b>,
    instr: &'b llvm_ir::Instruction,
    prog: &Program<'b,V>,
    inp: &ProgramInput<'b,V>,
    prog_inp: Transf<Em>,
    inp_inp: Transf<Em>,
    exprs: &[Em::Expr],
    em: &mut Em)
    -> Result<(Program<'b,V>,
               Transf<Em>),TrErr<'b,V,Em::Error>>
    where V : 'b+Bytes+FromConst<'b>+IntValue+Vector+Pointer<'b>+Debug,
          Cfg : TranslationCfg<Em>,
          Lib : Library<'b,V>,
          Em : DeriveValues {
    debug_assert_eq!(prog.num_elem(),prog_inp.size());
    debug_assert_eq!(inp.num_elem(),inp_inp.size());
    let (step,thr_idx) = if prog.is_single_threaded() {
        let idx = em.const_bitvec(STEP_BW,BigUint::from(0 as u8))?;
        (None,Transformation::constant(vec![idx]))
    } else {
        match program_input_thread_activation(inp,inp_inp,&thread_id,em)? {
            Some((step,idx)) => (Some(step),idx),
            None => {
                let mut rinp = inp.clone();
                rinp.add_thread(thread_id.clone());
                return Err(TrErr::InputNeeded(rinp))
            }
        }
    };

    
    let mut conds = Vec::new();
    let mut nprog = prog.clone();
    let mut updates = Vec::new();

    let threads_view = ThreadsView::new();
    let thread_pool_view = threads_view.then(AssocView::new(thread_id));
    
    let thread_pool = match thread_pool_view.get_el_opt(prog) {
        None => return Ok((nprog,finish_updates(updates,prog_inp))),
        Some(p) => p
    };

    let mut thread_iter = access_dyn(thread_pool,thr_idx,exprs,em)?;
    // Used only for debugging
    let mut any_call_frames = false;
    // Iterate over all possible active threads
    while let Some(thread_idx) = thread_iter.next(&mut conds,0,em)? {
        cfg.change_thread_activation(&mut conds,0,em)?;
        //println!("THREAD!");
        let thread_view = thread_pool_view.clone().then(VecView::new(thread_idx));

        let stack_top_view = thread_view.clone().then(StackTopView::new());

        let (stack_top,stack_top_inp) = stack_top_view.get_with_inp(prog,prog_inp.clone());

        let mut top_context_id_iter = stack_top.chosen(stack_top_inp.clone());

        let cpos = conds.len();
        while let Some(context_id_view) = top_context_id_iter.next(&mut conds,cpos,em)? {
            cfg.change_context_activation(&mut conds,cpos,em)?;
            //println!("CONTEXT!");
            let context_id = &context_id_view.get_el(stack_top).0;

            // Handle only matching contexts
            let fr_id = match context_id {
                &None => continue,
                &Some(ContextId::Call(ref cid_)) => if cf_id!=*cid_ {
                    continue
                } else {
                    None
                },
                &Some(ContextId::Stack(ref cid_,ref id_)) => if cf_id!=*cid_ {
                    continue
                } else {
                    Some(id_)
                }
            };

            let call_stack_view = thread_view.clone().then(CallStackView::new()).then(AssocView::new(cf_id));

            let (call_stack,call_stack_inp) = call_stack_view.get_with_inp(prog,prog_inp.clone());

            let mut call_frame_iter = call_stack.access_top(call_stack_inp.clone(),exprs,em)?;

            // Iterate over all active call frames
            let cpos = conds.len();
            while let Some(call_frame_view) = call_frame_iter.next(&mut conds,cpos,em)? {
                cfg.change_call_frame_activation(&mut conds,cpos,em)?;
                //println!("CALL FRAME!");
                
                let (call_frame,call_frame_inp) = call_frame_view.clone()
                    .then(FstView::new())
                    .get_with_inp(call_stack,call_stack_inp.clone());

                let (acts,acts_inp) = ActivationView::new()
                    .get_with_inp(call_frame,call_frame_inp.clone());

                // Add the instruction activation condition
                let cpos = conds.len();
                match acts.condition(acts_inp,&Data(instr_id),&mut conds,cpos) {
                    None => {
                        println!("Activation not found {:?}: {:?}",instr_id,acts);
                        continue
                    },
                    Some(_) => {}
                }
                cfg.change_instr_activation(&mut conds,cpos,em)?;
                // Used only for debugging
                any_call_frames = true;
                
                match instr.content {
                    llvm_ir::InstructionC::Alloca(ref name,ref tp,ref sz,_) => {
                        let dyn = match sz {
                            &None => None,
                            &Some(ref sz) => Some(translate_value(&m.datalayout,&sz.val,&sz.tp,&m.types,
                                                                  call_frame,call_frame_inp,
                                                                  exprs,em)?)
                        };
                        let stat_bits = m.datalayout.type_size_in_bits(tp,&m.types);
                        let stat_bytes = (stat_bits/8) as usize;
                        let (sl,sl_inp) = match dyn {
                            None => MemSlice::alloca(stat_bytes,em),
                            Some(_) => panic!("Dynamic sized allocations not supported")
                        };
                        let (ptr_,mut ptr_inp) = choice_empty();
                        let mut ptr = OptRef::Owned(ptr_);
                        match fr_id {
                            None => {
                                let fr_view = call_frame_view.clone()
                                    .then(SndView::new());
                                let allocs_view = fr_view.then(AllocationsView::new());
                                let alloc_pool_view = allocs_view.then(AssocView::new(instr_id));
                                let (alloc_pool,alloc_pool_inp)
                                    = match alloc_pool_view.get_opt_with_inp(call_stack,
                                                                             call_stack_inp.clone()) {
                                        None => (OptRef::Owned(Vec::new()),Transformation::id(0)),
                                        Some((p,inp)) => (OptRef::Ref(p),inp)
                                    };
                                let (alloc_idx,nalloc_pool,nalloc_pool_inp)
                                    = vec_pool_alloc(alloc_pool,OptRef::Owned(sl),
                                                     alloc_pool_inp,sl_inp,
                                                     &|_,_| false)?;
                                // Write the updates to the allocations
                                call_stack_view.clone()
                                    .then(alloc_pool_view)
                                    .insert(&mut nprog,nalloc_pool.as_obj(),nalloc_pool_inp,&mut updates);

                                // Generate the new pointer target
                                let trg = PointerTrg::Stack(thread_id,INDEX_WIDTH,
                                                            FrameId::Call(cf_id),INDEX_WIDTH,
                                                            instr_id.clone(),INDEX_WIDTH);
                                let thread_idx_inp = {
                                    let e = em.const_bitvec(INDEX_WIDTH,BigUint::from(thread_idx))?;
                                    Transformation::constant(vec![e])
                                };
                                let fr_idx_inp = {
                                    let e = em.const_bitvec(INDEX_WIDTH,BigUint::from(call_frame_view.idx))?;
                                    Transformation::constant(vec![e])
                                };
                                let alloc_idx_inp = {
                                    let e = em.const_bitvec(INDEX_WIDTH,BigUint::from(alloc_idx))?;
                                    Transformation::constant(vec![e])
                                };
                                let trg_inp = Transformation::concat(&[thread_idx_inp,
                                                                       fr_idx_inp,
                                                                       alloc_idx_inp]);
                                let rcond = if conds.len()==0 {
                                    Transformation::const_bool(true,em)?
                                } else {
                                    Transformation::and(conds.clone())
                                };
                                let (nptr,nptr_inp) = choice_insert(ptr,ptr_inp,rcond,
                                                                    OptRef::Owned((trg,(Data((stat_bytes,0)),None))),trg_inp)?;
                                ptr = nptr;
                                ptr_inp = nptr_inp;
                            },
                            Some(_) => unimplemented!()
                        }
                        // Insert the pointer
                        let value_view = call_stack_view.clone()
                            .then(call_frame_view.clone())
                            .then(FstView::new())
                            .then(ValuesView::new())
                            .then(AssocView::new(name));
                        let (val,val_inp) = V::from_pointer(m.datalayout.pointer_alignment(0).0 as usize,
                                                            ptr,ptr_inp);
                        value_view.insert_cond(&mut nprog,val.as_obj(),val_inp,&conds,&mut updates,prog_inp.clone(),em)?;

                        // Update instruction activation
                        let act_view = call_stack_view.clone()
                            .then(call_frame_view)
                            .then(FstView::new())
                            .then(ActivationView::new());
                        update_activation(&act_view,&mut nprog,&conds,
                                          instr_id.next(),
                                          &mut updates,
                                          prog_inp.clone(),
                                          em)?;
                    },
                    llvm_ir::InstructionC::Call(ref ret,_,ref ret_tp,ref called,ref args,_) => {
                        //println!("CALL!");
                        // Create the function type of the call
                        let arg_tps = args.iter().map(|v| v.tp.clone()).collect();
                        let ftp = llvm_ir::types::Type::Function(match ret_tp {
                            &Some((ref t,_)) => Some(Box::new(t.clone())),
                            &None => None
                        },arg_tps,false);
                        
                        // Update instruction activation
                        let act_view = call_stack_view.clone()
                            .then(call_frame_view.clone())
                            .then(FstView::new())
                            .then(ActivationView::new());
                        update_activation(&act_view,&mut nprog,&conds,
                                          instr_id.next(),
                                          &mut updates,
                                          prog_inp.clone(),
                                          em)?;

                        // Translate the called value
                        let (rcalled,rcalled_inp) = translate_value(&m.datalayout,called,&ftp,&m.types,
                                                                    call_frame,call_frame_inp.clone(),
                                                                    exprs,em)?;
                        let (base,base_inp) = match V::to_pointer(OptRef::Owned(rcalled),rcalled_inp) {
                            None => panic!("Called value not a pointer"),
                            Some(r) => r
                        };
                        let mut trgs = base.as_ref().chosen(base_inp.clone());
                        let cpos = conds.len();
                        while let Some(trg_view) = trgs.next(&mut conds,cpos,em)? {
                            let (trg,trg_inp) = trg_view.get_with_inp(base.as_ref(),base_inp.clone());
                            match trg {
                                &(PointerTrg::Global(name),_) => match name.as_ref() {
                                    "llvm.dbg.value" => { /* ignore */ },
                                    "llvm.dbg.declare" => { /* ignore */ },
                                    _ => {
                                        let mut targs = Vec::with_capacity(args.len());
                                        let mut targs_inp_ = Vec::with_capacity(args.len());
                                        for arg in args.iter() {
                                            let (targ,targ_inp) = translate_value(&m.datalayout,&arg.val,&arg.tp,&m.types,
                                                                                  call_frame,call_frame_inp.clone(),
                                                                                  exprs,em)?;
                                            targs.push(targ);
                                            targs_inp_.push(targ_inp);
                                        }
                                        let targs_inp = Transformation::concat(&targs_inp_[..]);
                                        let ret_view = match ret {
                                            &None => None,
                                            &Some(ref rname) => Some(call_stack_view.clone()
                                                                     .then(call_frame_view.clone())
                                                                     .then(FstView::new())
                                                                     .then(ValuesView::new())
                                                                     .then(AssocView::new(rname)))
                                        };
                                        let implemented = lib.call(name,
                                                                   &targs,targs_inp,
                                                                   ret_view,
                                                                   &m.datalayout,
                                                                   instr_id,
                                                                   &mut conds,
                                                                   &prog,
                                                                   prog_inp.clone(),
                                                                   &mut nprog,
                                                                   &mut updates,
                                                                   exprs,
                                                                   em)?;
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
                                            let (vals,vals_inp) = assoc_empty()?;
                                            let mut arg_vals = Vec::with_capacity(args.len());
                                            let mut arg_vals_inp_ = Vec::with_capacity(args.len());
                                            for arg in args.iter() {
                                                let (rarg,rarg_inp) = translate_value(&m.datalayout,&arg.val,&arg.tp,
                                                                                      &m.types,
                                                                                      call_frame,
                                                                                      call_frame_inp.clone(),
                                                                                      exprs,em)?;
                                                arg_vals.push(rarg);
                                                arg_vals_inp_.push(rarg_inp);
                                            }
                                            let arg_vals_inp = Transformation::concat(&arg_vals_inp_[..]);
                                            let (act0,act0_inp) = choice_empty();
                                            let (act,act_inp) = choice_insert(OptRef::Owned(act0),act0_inp,
                                                                              Transformation::const_bool(true,em)?,
                                                                              OptRef::Owned(Data(nxt_instr)),
                                                                              Transformation::id(0))?;
                                            let (phi,phi_inp) = choice_empty();
                                            let cf = CallFrame { values: vals.as_obj(),
                                                                 arguments: arg_vals,
                                                                 activation: act.as_obj(),
                                                                 phi: phi };
                                            
                                            let (prev_,prev_inp_) = choice_empty();
                                            let (prev,prev_inp) = choice_insert(OptRef::Owned(prev_),prev_inp_,
                                                                                Transformation::const_bool(true,em)?,
                                                                                OptRef::Owned(Data(context_id.clone())),
                                                                                Transformation::id(0))?;
                                            let (allocs,allocs_inp) = assoc_empty()?;
                                            let fr = Frame { previous: prev.as_obj(),
                                                             allocations: allocs.as_obj() };
                                            let cf_fr_inp = Transformation::concat(&[vals_inp,
                                                                                     arg_vals_inp,
                                                                                     act_inp,
                                                                                     phi_inp,
                                                                                     prev_inp,
                                                                                     allocs_inp]);
                                            // Insert the call frame
                                            let ncall_id = (Some(instr_id),name);
                                            let ncall_stack_view = thread_view.clone()
                                                .then(CallStackView::new())
                                                .then(AssocView::new(ncall_id));
                                            let (cur_cs_,cur_cs_inp)
                                                = match ncall_stack_view.get_opt_with_inp(prog,prog_inp.clone()) {
                                                    None => {
                                                        let (st,st_inp) = bv_vec_stack_empty(INDEX_WIDTH,em)?;
                                                        (OptRef::Owned(st),st_inp)
                                                    },
                                                    Some((r,inp)) => (OptRef::Ref(r),inp)
                                                };
                                            let mut cur_cs = cur_cs_.as_obj();
                                            let ncur_cs_inp = cur_cs.push_cond(cur_cs_inp,
                                                                               (cf,fr),cf_fr_inp,
                                                                               &mut conds,
                                                                               exprs,em)?;
                                            ncall_stack_view.insert(&mut nprog,cur_cs,ncur_cs_inp,&mut updates);
                                            // Update the stack top
                                            let (rstack_top,rstack_top_inp,rcond) = if conds.len()==0 {
                                                let c = em.const_bool(true)?;
                                                let (st,st_inp) = choice_empty();
                                                (OptRef::Owned(st),st_inp,Transformation::constant(vec![c]))
                                            } else {
                                                let c = Transformation::and(conds.to_vec());
                                                (OptRef::Ref(stack_top),stack_top_inp.clone(),c)
                                            };
                                            let (nstack_top,nstack_top_inp)
                                                = choice_set_chosen(rstack_top,rstack_top_inp.clone(),
                                                                    rcond,
                                                                    OptRef::Owned(Data(Some(ContextId::Call(ncall_id)))),
                                                                    Transformation::id(0))?;
                                            stack_top_view.write(nstack_top.as_obj(),nstack_top_inp,
                                                                 &mut nprog,&mut updates);
                                        }
                                    }
                                },
                                _ => panic!("Called object not a function")
                            }
                        }
                    },
                    llvm_ir::InstructionC::Unary(ref name,ref arg,ref op) => {
                        // Update instruction activation
                        let act_view = call_stack_view.clone()
                            .then(call_frame_view.clone())
                            .then(FstView::new())
                            .then(ActivationView::new());
                        update_activation(&act_view,&mut nprog,&conds,
                                          instr_id.next(),
                                          &mut updates,
                                          prog_inp.clone(),
                                          em)?;
                        let value_view = call_stack_view.clone()
                            .then(call_frame_view.clone())
                            .then(FstView::new())
                            .then(ValuesView::new())
                            .then(AssocView::new(name));
                        let (rarg,rarg_inp) = translate_value(&m.datalayout,&arg.val,&arg.tp,&m.types,
                                                              call_frame,call_frame_inp,
                                                              exprs,em)?;
                        match op {
                            &llvm_ir::UnaryInst::Cast(ref tp,ref op) => match op {
                                &llvm_ir::CastInst::Bitcast => {
                                    // Pointer casts are ignored, just copy the argument
                                    let (nval,nval_inp) = match value_view.get_opt_with_inp(&prog,prog_inp.clone()) {
                                        None => (OptRef::Owned(rarg),rarg_inp),
                                        Some((oval,oval_inp)) => {
                                            let rcond = if conds.len()==0 {
                                                let c = em.const_bool(true)?;
                                                Transformation::constant(vec![c])
                                            } else {
                                                Transformation::and(conds.to_vec())
                                            };
                                            ite(OptRef::Owned(rarg),OptRef::Ref(oval),rcond,rarg_inp,oval_inp,em)?.unwrap()
                                        }
                                    };
                                    value_view.insert(&mut nprog,nval.as_obj(),nval_inp,&mut updates);
                                },
                                &llvm_ir::CastInst::SExt => {
                                    let nsz = match tp {
                                        &llvm_ir::types::Type::Int(w) => w,
                                        _ => panic!("sext target not an int")
                                    };
                                    let (nval,nval_inp) = V::sext(OptRef::Owned(rarg),rarg_inp,nsz as usize,em);
                                    value_view.insert_cond(&mut nprog,
                                                           nval.as_obj(),nval_inp,
                                                           &conds,
                                                           &mut updates,
                                                           prog_inp.clone(),
                                                           em)?;
                                },
                                &llvm_ir::CastInst::ZExt => {
                                    let nsz = match tp {
                                        &llvm_ir::types::Type::Int(w) => w,
                                        _ => panic!("zext target not an int")
                                    };
                                    let (nval,nval_inp) = V::zext(OptRef::Owned(rarg),rarg_inp,nsz as usize,em);
                                    value_view.insert_cond(&mut nprog,
                                                           nval.as_obj(),nval_inp,
                                                           &conds,
                                                           &mut updates,
                                                           prog_inp.clone(),
                                                           em)?;
                                },
                                &llvm_ir::CastInst::Trunc => {
                                    let nsz = match tp {
                                        &llvm_ir::types::Type::Int(w) => w,
                                        _ => panic!("trunc target not an int")
                                    };
                                    let (nval,nval_inp) = V::trunc(OptRef::Owned(rarg),rarg_inp,nsz as usize,em);
                                    value_view.insert_cond(&mut nprog,
                                                           nval.as_obj(),nval_inp,
                                                           &conds,
                                                           &mut updates,
                                                           prog_inp.clone(),
                                                           em)?;
                                },
                                &llvm_ir::CastInst::IntToPtr => {
                                    value_view.insert_cond(&mut nprog,rarg,rarg_inp,&conds,
                                                           &mut updates,prog_inp.clone(),em)?;
                                },
                                &llvm_ir::CastInst::PtrToInt => {
                                    value_view.insert_cond(&mut nprog,rarg,rarg_inp,&conds,
                                                           &mut updates,prog_inp.clone(),em)?;
                                },
                                _ => panic!("Unsupported cast: {:?}",op)
                            },
                            &llvm_ir::UnaryInst::Load(_,_) => {
                                let sz = match arg.tp {
                                    llvm_ir::types::Type::Pointer(ref tp_,_)
                                        => (m.datalayout.type_size_in_bits(tp_,&m.types)/8) as usize,
                                    _ => panic!("Load argument not a pointer")
                                };
                                let value_view = call_stack_view.clone()
                                    .then(call_frame_view.clone())
                                    .then(FstView::new())
                                    .then(ValuesView::new())
                                    .then(AssocView::new(name));
                                let (ptr,ptr_inp) = match V::to_pointer(
                                    OptRef::Owned(rarg),
                                    rarg_inp) {

                                    None => panic!("Load argument isn't a pointer"),
                                    Some(r) => r
                                };
                                //println!("LOAD from {:#?}",ptr.as_ref());
                                let mut ptr_iter = ptr.as_ref().chosen(ptr_inp.clone());
                                let cpos = conds.len();
                                while let Some(base_view) = ptr_iter.next(&mut conds,cpos,em)? {
                                    let (trg_off,trg_off_inp)
                                        = base_view.get_with_inp(ptr.as_ref(),
                                                                 ptr_inp.clone());
                                    let &(ref trg,ref off) = trg_off;
                                    //println!("TARGET {:#?}",trg);
                                    let trg_sz = trg.num_elem();
                                    let trg_inp = Transformation::view(0,trg_sz,trg_off_inp.clone());
                                    let off_inp = Transformation::view(trg_sz,trg_off_inp.size()-trg_sz,trg_off_inp);
                                    let mut lookup_iter : MemLookups<V,Em>
                                        = MemLookups::new(trg,
                                                          trg_inp,
                                                          &prog,
                                                          exprs,
                                                          em)?;
                                    let cpos = conds.len();
                                    while let Some(lookup) = lookup_iter.next(&mut conds,cpos,em)? {
                                        let (load,load_inp) = lookup.load(&m.datalayout,
                                                                          off,off_inp.clone(),
                                                                          sz,prog,prog_inp.clone(),em)?;
                                        value_view.insert_cond(&mut nprog,
                                                               load.as_obj(),load_inp,
                                                               &conds,
                                                               &mut updates,
                                                               prog_inp.clone(),
                                                               em)?;
                                    }
                                }
                            }
                        }
                    },
                    llvm_ir::InstructionC::Select(ref name,ref sel,ref tp,ref if_t,ref if_f) => {
                        // Update instruction activation
                        let act_view = call_stack_view.clone()
                            .then(call_frame_view.clone())
                            .then(FstView::new())
                            .then(ActivationView::new());
                        update_activation(&act_view,&mut nprog,&conds,
                                          instr_id.next(),
                                          &mut updates,
                                          prog_inp.clone(),
                                          em)?;
                        let sel_tp = llvm_ir::types::Type::Int(1);
                        let (rsel,rsel_inp) = translate_value(&m.datalayout,sel,&sel_tp,&m.types,
                                                              call_frame,call_frame_inp.clone(),
                                                              exprs,em)?;
                        let cond = V::to_bool(OptRef::Owned(rsel),rsel_inp)?;
                        let (rif_t,rif_t_inp) = translate_value(&m.datalayout,if_t,tp,&m.types,
                                                                call_frame,call_frame_inp.clone(),
                                                                exprs,em)?;
                        let (rif_f,rif_f_inp) = translate_value(&m.datalayout,if_f,tp,&m.types,
                                                                call_frame,call_frame_inp,
                                                                exprs,em)?;
                        let (res,res_inp) = ite(OptRef::Owned(rif_t),
                                                OptRef::Owned(rif_f),
                                                cond,
                                                rif_t_inp,
                                                rif_f_inp,em)?.unwrap();
                        // Insert the result
                        let value_view = call_stack_view.clone()
                            .then(call_frame_view.clone())
                            .then(FstView::new())
                            .then(ValuesView::new())
                            .then(AssocView::new(name));
                        value_view.insert_cond(&mut nprog,
                                               res.as_obj(),res_inp,
                                               &conds,
                                               &mut updates,
                                               prog_inp.clone(),
                                               em)?;
                    },
                    llvm_ir::InstructionC::GEP(ref name,llvm_ir::GEP {
                        ref ptr,ref indices,..
                    }) => {
                        // Update instruction activation
                        let act_view = call_stack_view.clone()
                            .then(call_frame_view.clone())
                            .then(FstView::new())
                            .then(ActivationView::new());
                        update_activation(&act_view,&mut nprog,&conds,
                                          instr_id.next(),
                                          &mut updates,
                                          prog_inp.clone(),
                                          em)?;
                        // Calculate the GEP
                        let (rptr,rptr_inp) = translate_value(
                            &m.datalayout,&ptr.val,&ptr.tp,&m.types,
                            call_frame,call_frame_inp.clone(),
                            exprs,em)?;
                        let bw = rptr.byte_width();
                        let (base,base_inp) = V::to_pointer(
                            OptRef::Owned(rptr),
                            rptr_inp).unwrap();
                        let mut idx = Vec::with_capacity(indices.len());
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
                                        idx.push((None,coff as usize));
                                        &sub_tps[rc];
                                        break
                                    },
                                    _ => panic!("Struct not indexed by int")
                                },
                                &Type::Pointer(ref ptr_tp,_) => {
                                    let sz = m.datalayout.type_size_in_bits(
                                        ptr_tp,&m.types)/8;
                                    let (i,i_inp) = translate_value(
                                        &m.datalayout,
                                        &el.val,&el.tp,
                                        &m.types,
                                        call_frame,call_frame_inp.clone(),
                                        exprs,em)?;
                                    let (off,off_inp) = V::to_offset(OptRef::Owned(i),i_inp);
                                    let off_e = off_inp.get(exprs,0,em)?;
                                    match em.derive_const(&off_e)? {
                                        None => panic!("Dynamic GEP"),//idx.push((Some((off,off_inp)),sz as usize)),
                                        Some(off_c) => idx.push((None,value_as_index(&off_c)*(sz as usize)))
                                    };
                                    ptr_tp
                                },
                                &Type::Array(_,ref el_tp) => {
                                    let sz = m.datalayout.type_size_in_bits(
                                        el_tp,&m.types)/8;
                                    let (i,i_inp) = translate_value(
                                        &m.datalayout,
                                        &el.val,&el.tp,
                                        &m.types,
                                        call_frame,call_frame_inp.clone(),
                                        exprs,em)?;
                                    let (off,off_inp) = V::to_offset(OptRef::Owned(i),i_inp);
                                    let off_e = off_inp.get(exprs,0,em)?;
                                    match em.derive_const(&off_e)? {
                                        None => panic!("Dynamic GEP"),//idx.push((Some((off,off_inp)),sz as usize)),
                                        Some(off_c) => idx.push((None,value_as_index(&off_c)*(sz as usize)))
                                    };
                                    el_tp
                                },
                                _ => panic!("GEP for {:?}",cur_tp)
                            };
                        }
                        let (nbase,nbase_inp) = base_pointer_gep(
                            base,base_inp,idx,em)?;
                        let (nptr,nptr_inp) = V::from_pointer(bw,nbase,
                                                              nbase_inp);
                        // Write the pointer
                        let value_view = call_stack_view.clone()
                            .then(call_frame_view.clone())
                            .then(FstView::new())
                            .then(ValuesView::new())
                            .then(AssocView::new(name));
                        value_view.insert_cond(&mut nprog,
                                               nptr.as_obj(),nptr_inp,
                                               &conds,
                                               &mut updates,
                                               prog_inp.clone(),
                                               em)?;
                    },
                    llvm_ir::InstructionC::Store(_,ref val,ref ptr,_) => {
                        // Update instruction activation
                        let act_view = call_stack_view.clone()
                            .then(call_frame_view.clone())
                            .then(FstView::new())
                            .then(ActivationView::new());
                        update_activation(&act_view,&mut nprog,&conds,
                                          instr_id.next(),
                                          &mut updates,
                                          prog_inp.clone(),
                                          em)?;
                        let (rptr_,rptr_inp_) = translate_value(&m.datalayout,&ptr.val,&ptr.tp,
                                                                &m.types,
                                                                call_frame,
                                                                call_frame_inp.clone(),
                                                                exprs,em)?;
                        let (rptr,rptr_inp) = match V::to_pointer(
                            OptRef::Owned(rptr_),
                            rptr_inp_) {
                            None => panic!("Store target isn't a pointer"),
                            Some(r) => r
                        };
                        /*println!("STORE to {:?}, {:?}, {:?}",rptr.as_ref(),rptr_inp,
                                 rptr_inp.get_all(exprs,em)?.iter().map(|e| match em.derive_values(e).unwrap() {
                                     None => vec![],
                                     Some(v) => v.collect::<Vec<_>>()
                                 }).collect::<Vec<_>>() );*/
                        let (rval,rval_inp) = translate_value(&m.datalayout,&val.val,&val.tp,
                                                              &m.types,
                                                              call_frame,
                                                              call_frame_inp.clone(),
                                                              exprs,em)?;
                        let mut ptr_iter = rptr.as_ref().chosen(rptr_inp.clone());
                        let cpos = conds.len();
                        while let Some(base_view) = ptr_iter.next(&mut conds,cpos,em)? {
                            let (trg_off,trg_off_inp)
                                = base_view.get_with_inp(rptr.as_ref(),
                                                         rptr_inp.clone());
                            //println!("STORE TRG {:?}",trg_off_inp);
                            let &(ref trg,ref off) = trg_off;
                            let trg_sz = trg.num_elem();
                            let trg_inp = Transformation::view(0,trg_sz,trg_off_inp.clone());
                            let off_inp = Transformation::view(trg_sz,trg_off_inp.size()-trg_sz,trg_off_inp);
                            let mut lookup_iter : MemLookups<V,Em>
                                = MemLookups::new(trg,
                                                  trg_inp,
                                                  &prog,
                                                  exprs,
                                                  em)?;
                            let cpos = conds.len();
                            while let Some(lookup) = lookup_iter.next(&mut conds,cpos,em)? {
                                //println!("STORE LOOKUP");
                                if conds.len()==0 {
                                    lookup.store(off,off_inp.clone(),&rval,rval_inp.clone(),
                                                 &mut nprog,&mut updates,
                                                 prog_inp.clone(),em)?;
                                } else {
                                    let bw = rval.byte_width();
                                    let rcond = Transformation::and(conds.clone());
                                    let (pval,pval_inp) = lookup.load(&m.datalayout,
                                                                      off,off_inp.clone(),bw,
                                                                      &prog,prog_inp.clone(),
                                                                      em)?;
                                    let (nval,nval_inp) = ite(OptRef::Ref(&rval),
                                                              pval,
                                                              rcond,
                                                              rval_inp.clone(),
                                                              pval_inp,em)?.unwrap();
                                    lookup.store(off,off_inp.clone(),nval.as_ref(),nval_inp,
                                                 &mut nprog,&mut updates,
                                                 prog_inp.clone(),em)?;
                                }
                            }
                        }
                    },
                    llvm_ir::InstructionC::Bin(ref name,ref op,ref tp,ref lhs,ref rhs) => {
                        // Update instruction activation
                        let act_view = call_stack_view.clone()
                            .then(call_frame_view.clone())
                            .then(FstView::new())
                            .then(ActivationView::new());
                        update_activation(&act_view,&mut nprog,&conds,
                                          instr_id.next(),
                                          &mut updates,
                                          prog_inp.clone(),
                                          em)?;
                        let (val_l,val_l_inp) = translate_value(&m.datalayout,
                                                                lhs,tp,
                                                                &m.types,
                                                                call_frame,
                                                                call_frame_inp.clone(),
                                                                exprs,em)?;
                        let (val_r,val_r_inp) = translate_value(&m.datalayout,
                                                                rhs,tp,
                                                                &m.types,
                                                                call_frame,
                                                                call_frame_inp.clone(),
                                                                exprs,em)?;
                        let (res,res_inp) = V::bin(op,
                                                   &val_l,
                                                   &val_r,
                                                   val_l_inp,val_r_inp,
                                                   exprs,
                                                   em)?;
                        let value_view = call_stack_view.clone()
                            .then(call_frame_view.clone())
                            .then(FstView::new())
                            .then(ValuesView::new())
                            .then(AssocView::new(name));
                        value_view.insert_cond(&mut nprog,
                                               res,res_inp,
                                               &conds,
                                               &mut updates,
                                               prog_inp.clone(),
                                               em)?;
                    },
                    llvm_ir::InstructionC::Term(llvm_ir::Terminator::Ret(ref retv)) => {
                        let rret = match retv {
                            &None => None,
                            &Some(ref r) => Some(translate_value(&m.datalayout,
                                                                 &r.val,&r.tp,
                                                                 &m.types,
                                                                 call_frame,
                                                                 call_frame_inp.clone(),
                                                                 exprs,em)?)
                        };
                        match fr_id {
                            None => {
                                let prev_view = call_frame_view.clone()
                                    .then(SndView::new())
                                    .then(PrevFrameView::new());
                                let (prev,prev_inp) = prev_view.get_with_inp(&call_stack,call_stack_inp.clone());
                                let mut prev_it = prev.chosen(prev_inp.clone());
                                match rret {
                                    None => {},
                                    Some((ret,ret_inp)) => {
                                        let cpos = conds.len();
                                        while let Some(ctx_view) = prev_it.next(&mut conds,cpos,em)? {
                                            let ctx = ctx_view.get_el(&prev);
                                            match ctx.0 {
                                                None => {
                                                    panic!("Handle thread return")
                                                },
                                                Some(ref ctx_) => {
                                                    let pcall = match ctx_ {
                                                        &ContextId::Call(c) => c,
                                                        &ContextId::Stack(c,_) => c
                                                    };
                                                    let pstack_view = thread_view.clone()
                                                        .then(CallStackView::new())
                                                        .then(AssocView::new(pcall));
                                                    let (pstack,pstack_inp) = pstack_view.get_with_inp(prog,prog_inp.clone());
                                                    let mut pstack_it = pstack.access_top(pstack_inp,exprs,em)?;
                                                    let cpos = conds.len();
                                                    while let Some(pcf_view) = pstack_it.next(&mut conds,cpos,em)? {
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
                                                        let ret_val_view = pstack_view.clone()
                                                            .then(pcf_view)
                                                            .then(FstView::new())
                                                            .then(ValuesView::new())
                                                            .then(AssocView::new(ret_instr));
                                                        ret_val_view.insert_cond(&mut nprog,
                                                                                 ret.clone(),ret_inp.clone(),
                                                                                 &conds,
                                                                                 &mut updates,
                                                                                 prog_inp.clone(),
                                                                                 em)?
                                                    }
                                                }
                                            }
                                        }
                                    }
                                };
                                stack_top_view.write_cond(prev.clone(),
                                                          prev_inp,
                                                          &mut nprog,
                                                          &conds,
                                                          &mut updates,
                                                          prog_inp.clone(),
                                                          em)?;
                                let (ncall_stack,ncall_stack_inp)
                                    = bv_vec_stack_pop(OptRef::Ref(call_stack),call_stack_inp.clone(),exprs,em)?.unwrap();
                                call_stack_view.write_cond(ncall_stack.as_obj(),
                                                           ncall_stack_inp,
                                                           &mut nprog,
                                                           &conds,
                                                           &mut updates,
                                                           prog_inp.clone(),
                                                           em)?;
                            },
                            Some(_) => unimplemented!()
                        }
                    },
                    llvm_ir::InstructionC::ICmp(ref name,ref op,ref tp,ref lhs,ref rhs) => {
                        // Update instruction activation
                        let act_view = call_stack_view.clone()
                            .then(call_frame_view.clone())
                            .then(FstView::new())
                            .then(ActivationView::new());
                        update_activation(&act_view,&mut nprog,&conds,
                                          instr_id.next(),
                                          &mut updates,
                                          prog_inp.clone(),
                                          em)?;
                        let (vl,vl_inp) = translate_value(&m.datalayout,
                                                          lhs,tp,
                                                          &m.types,
                                                          call_frame,call_frame_inp.clone(),
                                                          exprs,em)?;
                        let (vr,vr_inp) = translate_value(&m.datalayout,
                                                          rhs,tp,
                                                          &m.types,
                                                          call_frame,call_frame_inp.clone(),
                                                          exprs,em)?;
                        let cond = V::icmp(op,
                                           &vl,vl_inp,
                                           &vr,vr_inp,em)?;
                        let (ret,ret_inp) = V::from_bool(cond)?;
                        let value_view = call_stack_view.clone()
                            .then(call_frame_view.clone())
                            .then(FstView::new())
                            .then(ValuesView::new())
                            .then(AssocView::new(name));
                        value_view.insert_cond(&mut nprog,
                                               ret,ret_inp,
                                               &conds,
                                               &mut updates,
                                               prog_inp.clone(),
                                               em)?;
                    },
                    llvm_ir::InstructionC::Term(llvm_ir::Terminator::BrC(ref cond,ref trgT,ref trgF)) => {
                        let instrT = InstructionRef { function: instr_id.function,
                                                      basic_block: trgT,
                                                      instruction: 0 };
                        let instrF = InstructionRef { function: instr_id.function,
                                                      basic_block: trgF,
                                                      instruction: 0 };
                        
                        let tp = llvm_ir::types::Type::Int(1);
                        let (rcond,rcond_inp) = translate_value(&m.datalayout,
                                                                cond,&tp,
                                                                &m.types,
                                                                call_frame,call_frame_inp.clone(),
                                                                exprs,em)?;
                        let bcond = V::to_bool(OptRef::Owned(rcond),rcond_inp)?;
                        let ncond = Transformation::not(bcond.clone());
                        let (ch0,ch0_inp) = choice_empty();
                        let (ch1,ch1_inp) = choice_insert(OptRef::Owned(ch0),ch0_inp,
                                                          bcond.clone(),
                                                          OptRef::Owned(Data(instrT)),Transformation::id(0))?;
                        let (ch2,ch2_inp) = choice_insert(ch1,ch1_inp,
                                                          ncond.clone(),
                                                          OptRef::Owned(Data(instrF)),Transformation::id(0))?;
                        let act_view = call_stack_view.clone()
                            .then(call_frame_view.clone())
                            .then(FstView::new())
                            .then(ActivationView::new());
                        act_view.write_cond(ch2.as_obj(),ch2_inp,
                                            &mut nprog,&mut conds,&mut updates,prog_inp.clone(),em)?;
                        
                        // Evaluate phis

                        let phi_view = call_stack_view.clone()
                            .then(call_frame_view.clone())
                            .then(FstView::new())
                            .then(PhiView::new());
                        let (phi0,phi_inp0) = choice_empty();
                        let (phi1,phi_inp1) = choice_insert(OptRef::Owned(phi0),
                                                            phi_inp0,
                                                            bcond,
                                                            OptRef::Owned(Data((instr_id.basic_block,trgT))),
                                                            Transformation::id(0))?;
                        let (phi2,phi_inp2) = choice_insert(phi1,
                                                            phi_inp1,
                                                            ncond,
                                                            OptRef::Owned(Data((instr_id.basic_block,trgF))),
                                                            Transformation::id(0))?;
                        phi_view.write_cond(phi2.as_obj(),phi_inp2,
                                            &mut nprog,
                                            &conds,
                                            &mut updates,prog_inp.clone(),em)?;
                        /*
                        let values_view = call_stack_view.clone()
                            .then(call_frame_view.clone())
                            .then(FstView::new())
                            .then(ValuesView::new());
                        conds.push(bcond);
                        eval_phi(m,instr_id.function,instr_id.basic_block,trgT,&values_view,
                                 &call_frame,call_frame_inp.clone(),
                                 &conds,&mut nprog,&mut updates,prog_inp.clone(),
                                 exprs,em)?;
                        conds.pop();
                        conds.push(ncond);
                        eval_phi(m,instr_id.function,instr_id.basic_block,trgF,&values_view,
                                 &call_frame,call_frame_inp.clone(),
                                 &conds,&mut nprog,&mut updates,prog_inp.clone(),
                                 exprs,em)?;
                        conds.pop();*/
                    },
                    llvm_ir::InstructionC::Term(llvm_ir::Terminator::Br(ref trg)) => {
                        let instr_next = InstructionRef { function: instr_id.function,
                                                          basic_block: trg,
                                                          instruction: 0 };
                        // Update instruction activation
                        let act_view = call_stack_view.clone()
                            .then(call_frame_view.clone())
                            .then(FstView::new())
                            .then(ActivationView::new());
                        update_activation(&act_view,&mut nprog,&conds,
                                          instr_next,
                                          &mut updates,
                                          prog_inp.clone(),
                                          em)?;
                        // Evaluate phis
                        let phi_view = call_stack_view.clone()
                            .then(call_frame_view.clone())
                            .then(FstView::new())
                            .then(PhiView::new());
                        let (phi0,phi_inp0) = choice_empty();
                        let (phi1,phi_inp1) = choice_insert(OptRef::Owned(phi0),
                                                            phi_inp0,
                                                            Transformation::const_bool(true,em)?,
                                                            OptRef::Owned(Data((instr_id.basic_block,trg))),
                                                            Transformation::id(0))?;
                        phi_view.write_cond(phi1.as_obj(),phi_inp1,
                                            &mut nprog,
                                            &conds,
                                            &mut updates,prog_inp.clone(),em)?;
                        /*
                        let values_view = call_stack_view.clone()
                            .then(call_frame_view.clone())
                            .then(FstView::new())
                            .then(ValuesView::new());
                        eval_phi(m,instr_id.function,instr_id.basic_block,trg,&values_view,
                                 &call_frame,call_frame_inp,
                                 &conds,&mut nprog,&mut updates,prog_inp.clone(),
                                 exprs,em)?;*/
                    },
                    llvm_ir::InstructionC::Phi(ref name,ref tp,ref srcs) => {
                        // Update instruction activation
                        let act_view = call_stack_view.clone()
                            .then(call_frame_view.clone())
                            .then(FstView::new())
                            .then(ActivationView::new());
                        update_activation(&act_view,&mut nprog,&conds,
                                          instr_id.next(),
                                          &mut updates,
                                          prog_inp.clone(),
                                          em)?;
                        // Update value
                        let phi_view = call_stack_view.clone()
                            .then(call_frame_view.clone())
                            .then(FstView::new())
                            .then(PhiView::new());
                        let (phi,phi_inp) = phi_view.get_with_inp(&prog,prog_inp.clone());
                        let mut rval = None;
                        for &(ref val,ref src) in srcs.iter() {
                            let cpos = conds.len();
                            if let Some(e_inp) = phi.condition(
                                phi_inp.clone(),
                                &Data((&src,instr_id.basic_block)),
                                &mut conds,cpos) {

                                let mut rconds: Vec<_> = conds.drain(cpos..)
                                    .collect();
                                let rcond = match rconds.len() {
                                    0 => Transformation::const_bool(true,em)?,
                                    1 => rconds.remove(0),
                                    _ => Transformation::and(rconds)
                                };
                                let (nval,nval_inp) = translate_value(&m.datalayout,
                                                                      val,tp,
                                                                      &m.types,
                                                                      call_frame,call_frame_inp.clone(),
                                                                      exprs,em)?;
                                rval = match rval {
                                    None => Some((OptRef::Owned(nval),nval_inp)),
                                    Some((cval,cval_inp)) => Some(ite(OptRef::Owned(nval),
                                                                      cval,
                                                                      rcond,nval_inp,cval_inp,em)?.unwrap())
                                };
                            }
                        }
                        let value_view = call_stack_view.clone()
                            .then(call_frame_view.clone())
                            .then(FstView::new())
                            .then(ValuesView::new())
                            .then(AssocView::new(name));
                        let (nval,nval_inp) = rval.unwrap();
                        value_view.insert_cond(&mut nprog,nval.as_obj(),nval_inp,
                                               &conds,&mut updates,
                                               prog_inp.clone(),em)?;
                    },
                    _ => panic!("Cannot translate instruction {:#?}",instr)
                }
            }
        }
    }
    if !any_call_frames {
        panic!("No callframes found! {:#?}",prog.threads);
    }
    //println!("Threads: {:#?}",nprog.threads);
    Ok((nprog,finish_updates(updates,prog_inp)))
}

pub fn translate_value<'b,V,Em>(dl: &'b DataLayout,
                                value: &'b llvm_ir::Value,
                                tp: &Type,
                                tps: &'b HashMap<String,Type>,
                                cf: &CallFrame<'b,V>,
                                cf_inp: Transf<Em>,
                                _: &[Em::Expr],
                                em: &mut Em)
                                -> Result<(V,Transf<Em>),Em::Error>
    where V : 'b+Bytes+FromConst<'b>+Pointer<'b>+IntValue+Vector+Clone,Em : DeriveValues {
    match value {
        &llvm_ir::Value::Constant(ref c) => {
            let (obj,els) = translate_constant(dl,c,tp,tps,em)?;
            Ok((obj,els))
        },
        &llvm_ir::Value::Local(ref name) => {
            let val_view = ValuesView::new().then(AssocView::new(name));
            let (val,val_inp) = val_view.get_with_inp(cf,cf_inp);
            Ok((val.clone(),val_inp))
        },
        &llvm_ir::Value::Argument(n) => {
            let val_view = ArgumentsView::new().then(VecView::new(n));
            let (val,val_inp) = val_view.get_with_inp(cf,cf_inp);
            Ok((val.clone(),val_inp))
        },
        _ => panic!("Translate value: {:#?}",value)
    }
}

pub fn translate_constant<'b,V,Em>(dl: &'b DataLayout,
                                   c: &'b llvm_ir::Constant,
                                   tp: &Type,
                                   mp: &HashMap<String,Type>,
                                   em: &mut Em)
                                   -> Result<(V,Transf<Em>),Em::Error>
    where V : Bytes+Pointer<'b>+IntValue+Vector+Clone, Em : Embed {

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
            let (ptr,inp_ptr) = base_pointer_global(mult as usize,glb,em)?;
            let (bw,_,_) = dl.pointer_alignment(0);
            let (res,inp_res) = V::from_pointer((bw/8) as usize,
                                                OptRef::Owned(ptr),
                                                inp_ptr);
            Ok((res.as_obj(),inp_res))
        },
        &llvm_ir::Constant::Int(ref val) => match tp {
            &Type::Int(bw) => {
                let rval = match val.to_biguint() {
                    Some(r) => r,
                    None => match (-val).to_biguint() {
                        Some(neg_val) => BigUint::from(1 as u8).shl(bw as usize) - neg_val,
                        None => unreachable!()
                    }
                };
                let (rv,rv_inp) = V::const_int(bw,rval,em)?;
                Ok((rv,Transformation::constant(rv_inp)))
            },
            _ => panic!("Integer value with non-integer type")
        },
        &llvm_ir::Constant::Array(ref arr) => {
            let mut varr : Vec<V> = Vec::with_capacity(arr.len());
            let mut earr : Vec<Transf<Em>> = Vec::with_capacity(arr.len());
            let el_tp = match tp {
                &Type::Array(_,ref subtp) => subtp,
                _ => panic!("Array value with non-array type")
            };
            for el in arr.iter() {
                let (val,c) : (V,Transf<Em>) = translate_constant(dl,el,el_tp,mp,em)?;
                varr.push(val);
                earr.push(c);
            }
            let (res,inp_res) = V::vector(OptRef::Owned(varr),earr,em)?;
            Ok((res.as_obj(),inp_res))
        },
        &llvm_ir::Constant::GEP(ref gep) => {
            let mut cur_tp = &gep.ptr.tp;
            let mut res = Vec::with_capacity(gep.indices.len());
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
                            res.push((None,coff as usize));
                            &sub_tps[ridx]
                        },
                        _ => panic!("Struct not indexed by constant int")
                    },
                    &Type::Pointer(ref ptr_tp,_) => {
                        let sz = dl.type_size_in_bits(ptr_tp,mp)/8;
                        match el.val {
                            llvm_ir::Constant::Int(ref idx) => {
                                res.push((None,idx.to_usize().unwrap()*(sz as usize)))
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
                                res.push((None,idx.to_usize().unwrap()*(sz as usize)))
                            },
                            _ => panic!("Array not indexed properly")
                        }
                        sub_tp
                    },
                    _ => unimplemented!()
                }
            }
            let (base,base_inp) : (V,Transf<Em>) = translate_constant(dl,&gep.ptr.val,&gep.ptr.tp,mp,em)?;
            let bw = base.byte_width();
            let (ptr,ptr_inp) = V::to_pointer(OptRef::Owned(base),base_inp).expect("Cannot convert to pointer");
            let (nptr,nptr_inp) = base_pointer_gep(ptr,ptr_inp,res,em)?;
            let (res,inp_res) = V::from_pointer(bw,nptr,nptr_inp);
            Ok((res.as_obj(),inp_res))
        },
        &llvm_ir::Constant::NullPtr => {
            let bw = (dl.pointer_alignment(0).0 / 8) as usize;
            let (base,base_inp) = base_pointer_null(em)?;
            let (ptr,ptr_inp) = V::from_pointer(bw,OptRef::Owned(base),base_inp);
            Ok((ptr.as_obj(),ptr_inp))
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

pub fn translate_global<'b,V>(dl: &'b DataLayout,
                              c: &'b llvm_ir::Constant,
                              tp: &'b Type,
                              mp: &'b HashMap<String,Type>)
                              -> MemSlice<'b,V>
    where V : Bytes+Clone {
    let mut res = Vec::new();
    translate_global_(dl,c,tp,mp,&mut res);
    MemSlice(res)
}

fn translate_global_<'b,V>(dl: &'b DataLayout,
                           c: &'b llvm_ir::Constant,
                           tp: &'b Type,
                           mp: &'b HashMap<String,Type>,
                           res: &mut Vec<MemObj<'b,V>>)
                           -> ()
    where V : Bytes+Clone {

    match c {
        &llvm_ir::Constant::Array(ref arr) => {
            let el_tp = match tp {
                &Type::Array(_,ref subtp) => subtp,
                _ => panic!("Array value with non-array type")
            };
            for el in arr.iter() {
                translate_global_(dl,el,el_tp,mp,res);
            }
        },
        _ => {
            res.push(MemObj::ConstObj(dl,c,tp,mp));
        }
    }
}

pub trait IntValue : Composite {
    fn const_int<Em : Embed>(u64,BigUint,&mut Em) -> Result<(Self,Vec<Em::Expr>),Em::Error>;
    fn bin<'b,Em>(op: &llvm_ir::BinOp,
                  lhs: &Self,
                  rhs: &Self,
                  inp_l: Transf<Em>,
                  inp_r: Transf<Em>,
                  exprs: &[Em::Expr],
                  em: &mut Em)
                  -> Result<(Self,Transf<Em>),Em::Error>
        where Em : DeriveValues;
    fn sext<'a,Em>(OptRef<'a,Self>,Transf<Em>,usize,&mut Em)
                   -> (OptRef<'a,Self>,Transf<Em>)
        where Em : Embed;
    fn zext<'a,Em>(OptRef<'a,Self>,Transf<Em>,usize,&mut Em)
                   -> (OptRef<'a,Self>,Transf<Em>)
        where Em : Embed;
    fn trunc<'a,Em>(OptRef<'a,Self>,Transf<Em>,usize,&mut Em)
                   -> (OptRef<'a,Self>,Transf<Em>)
        where Em : Embed;
    fn icmp<Em>(&llvm_ir::CmpOp,
                &Self,Transf<Em>,
                &Self,Transf<Em>,
                &mut Em)
                -> Result<Transf<Em>,Em::Error>
        where Em : Embed;
    fn from_bool<Em : Embed>(Transf<Em>) -> Result<(Self,Transf<Em>),Em::Error>;
    fn to_bool<'a,Em : Embed>(OptRef<'a,Self>,Transf<Em>) -> Result<Transf<Em>,Em::Error>;
    fn to_offset<'a,Em : Embed>(OptRef<'a,Self>,Transf<Em>) -> (Singleton,Transf<Em>);
    fn from_offset<'a,Em : Embed>(usize,&Singleton,Transf<Em>)
                                  -> (Self,Transf<Em>);
}

/*pub trait Pointer<'a> : Composite {
    fn null<Em : Embed>(u64,&mut Em) -> Result<(Self,Vec<Em::Expr>),Em::Error>;
    fn global<Em : Embed>(u64,&'a String,&mut Em) -> Result<(Self,Vec<Em::Expr>),Em::Error>;
    fn gep<Em : Embed>(Self,
                       Transf<Em>,
                       Vec<(Option<(Self,Transf<Em>)>,u64)>,
                       &mut Em)
                       -> Result<(Self,Transf<Em>),Em::Error>;
}*/

pub trait Vector : Composite {
    fn vector<'a,Em : Embed>(OptRef<'a,Vec<Self>>,Vec<Transf<Em>>,&mut Em) -> Result<(OptRef<'a,Self>,Transf<Em>),Em::Error>;
}

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub enum CompValue<Ptr,V> {
    Value(V),
    Pointer(BitField<Ptr>),
    Vector(Vec<CompValue<Ptr,V>>)
}

#[derive(Clone)]
pub enum CompValueMeaning<Ptr : Semantic,V : Semantic> {
    Value(V::Meaning),
    Pointer(<BitField<Ptr> as Semantic>::Meaning),
    Vector(Box<VecMeaning<CompValueMeaning<Ptr,V>>>)
}

pub enum CompValueMeaningCtx<Ptr : Semantic,V : Semantic> {
    Value(V::MeaningCtx),
    Pointer(<BitField<Ptr> as Semantic>::MeaningCtx),
    Vector(Box<CompValueMeaningCtx<Ptr,V>>)
}

impl<V : Semantic,U : Semantic> PartialEq for CompValueMeaning<V,U> {
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

impl<V : Semantic,U : Semantic> Eq for CompValueMeaning<V,U> {}

impl<V : Semantic,U : Semantic> PartialOrd for CompValueMeaning<V,U> {
    fn partial_cmp(&self,other: &CompValueMeaning<V,U>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<V : Semantic,U : Semantic> Ord for CompValueMeaning<V,U> {
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

impl<V : Semantic,U : Semantic> Hash for CompValueMeaning<V,U> {
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

impl<V : Semantic,U : Semantic> fmt::Debug for CompValueMeaning<V,U> {
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

impl<Ptr : Semantic,V : Semantic> Semantic for CompValue<Ptr,V> {
    type Meaning = CompValueMeaning<Ptr,V>;
    type MeaningCtx = CompValueMeaningCtx<Ptr,V>;
    fn meaning(&self,pos: usize) -> Self::Meaning {
        match self {
            &CompValue::Value(ref v) => CompValueMeaning::Value(v.meaning(pos)),
            &CompValue::Pointer(ref p) => CompValueMeaning::Pointer(p.meaning(pos)),
            &CompValue::Vector(ref v) => CompValueMeaning::Vector(Box::new(v.meaning(pos)))
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
            }
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
            }
        }
    }
}

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub struct ByteWidth<V> {
    value: V,
    byte_width: usize
}

impl<V : Semantic> Semantic for ByteWidth<V> {
    type Meaning = V::Meaning;
    type MeaningCtx = V::MeaningCtx;
    fn meaning(&self,pos: usize) -> Self::Meaning {
        self.value.meaning(pos)
    }
    fn fmt_meaning<F : fmt::Write>(&self,m: &Self::Meaning,fmt: &mut F) -> Result<(),fmt::Error> {
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

impl Composite for BitVecValue {
    fn num_elem(&self) -> usize { 1 }
    fn elem_sort<Em : Embed>(&self,n:usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        assert_eq!(n,0);
        match *self {
            BitVecValue::BoolValue(_) => em.tp_bool(),
            BitVecValue::BitVecValue(sz) => em.tp_bitvec(sz)
        }
    }
    fn combine<'a,Em,FComb,FL,FR>(x: OptRef<'a,Self>,y: OptRef<'a,Self>,
                                  inp_x: Transf<Em>,inp_y: Transf<Em>,
                                  comb: &FComb,_: &FL,_: &FR,em: &mut Em)
                                  -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>
        where Em : Embed,
              FComb : Fn(Transf<Em>,Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FL : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FR : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error> {
    
        match *x.as_ref() {
            BitVecValue::BoolValue(sz1) => match *y.as_ref() {
                BitVecValue::BoolValue(sz2)
                    => if sz1==sz2 {
                        let outp = comb(inp_x,inp_y,em)?;
                        Ok(Some((OptRef::Owned(BitVecValue::BoolValue(sz1)),outp)))
                    } else {
                        Ok(None)
                    },
                BitVecValue::BitVecValue(sz2)
                    => if sz1==sz2 {
                        let f = move |_:&[Em::Expr],_:usize,e: Em::Expr,em: &mut Em| {
                            let bv0 = em.const_bitvec(sz1,BigUint::from(0 as u8))?;
                            let bv1 = em.const_bitvec(sz1,BigUint::from(1 as u8))?;
                            em.ite(e,bv1,bv0)
                        };
                        let ninp_x = Transformation::map_by_elem(Box::new(f),inp_x);
                        let outp = comb(ninp_x,inp_y,em)?;
                        Ok(Some((OptRef::Owned(BitVecValue::BitVecValue(sz1)),outp)))
                    } else {
                        Ok(None)
                    }
            },
            BitVecValue::BitVecValue(sz1) => match *y.as_ref() {
                BitVecValue::BoolValue(sz2) => if sz1==sz2 {
                    let f = move |_:&[Em::Expr],_:usize,e: Em::Expr,em: &mut Em| {
                            let bv0 = em.const_bitvec(sz1,BigUint::from(0 as u8))?;
                            let bv1 = em.const_bitvec(sz1,BigUint::from(1 as u8))?;
                            em.ite(e,bv1,bv0)
                        };
                    let ninp_y = Transformation::map_by_elem(Box::new(f),inp_y);
                    let outp = comb(inp_x,ninp_y,em)?;
                    Ok(Some((OptRef::Owned(BitVecValue::BitVecValue(sz1)),outp)))
                } else {
                    Ok(None)
                },
                BitVecValue::BitVecValue(sz2) => if sz1==sz2 {
                    let outp = comb(inp_x,inp_y,em)?;
                    Ok(Some((OptRef::Owned(BitVecValue::BitVecValue(sz2)),outp)))
                } else {
                    Ok(None)
                }
            }
        }
    }
}

impl IntValue for BitVecValue {
    fn to_offset<'a,Em : Embed>(v: OptRef<'a,Self>,tr: Transf<Em>) -> (Singleton,Transf<Em>) {
        let (tp,ntr) = match v.as_ref() {
            &BitVecValue::BoolValue(w) => {
                let f = move |_:&[Em::Expr],_:usize,e: Em::Expr,em: &mut Em| {
                    let zero = em.const_bitvec(w,BigUint::from(0 as u8))?;
                    let one  = em.const_bitvec(w,BigUint::from(1 as u8))?;
                    em.ite(e,one,zero)
                };
                (Sort::from_kind(SortKind::BitVec(w)),
                 Transformation::map_by_elem(Box::new(f),tr))
            },
            &BitVecValue::BitVecValue(w) => (Sort::from_kind(SortKind::BitVec(w)),tr)
        };
        (Singleton(tp),ntr)
    }
    fn from_offset<'a,Em : Embed>(bw: usize,tp: &Singleton,inp: Transf<Em>)
                                  -> (Self,Transf<Em>) {
        match tp.0.kind() {
            SortKind::Bool => (BitVecValue::BoolValue(bw),inp),
            SortKind::BitVec(w) => {
                assert_eq!(w,bw);
                (BitVecValue::BitVecValue(w),inp)
            },
            _ => unimplemented!()
        }
    }
    fn const_int<Em : Embed>(bw: u64,val: BigUint,em: &mut Em) -> Result<(BitVecValue,Vec<Em::Expr>),Em::Error> {
        if val==BigUint::from(0 as u8) || val==BigUint::from(1 as u8) {
            let el = em.const_bool(val==BigUint::from(1 as u8))?;
            Ok((BitVecValue::BoolValue(bw as usize),
                vec![el]))
        } else {
            let el = em.const_bitvec(bw as usize,val)?;
            Ok((BitVecValue::BitVecValue(bw as usize),
                vec![el]))
        }
    }
    fn bin<'b,Em>(op: &llvm_ir::BinOp,
                  lhs: &BitVecValue,
                  rhs: &BitVecValue,
                  inp_l: Transf<Em>,
                  inp_r: Transf<Em>,
                  _: &[Em::Expr],
                  _: &mut Em)
                  -> Result<(BitVecValue,Transf<Em>),Em::Error>
        where Em : DeriveValues {
        match op {
            &llvm_ir::BinOp::Add(_,_) => match *lhs {
                BitVecValue::BoolValue(sz1) => match *rhs {
                    BitVecValue::BoolValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let bv0 = em.const_bitvec(sz1,BigUint::from(0 as u8))?;
                            let bv1 = em.const_bitvec(sz1,BigUint::from(1 as u8))?;
                            let rlhs = em.ite(lhs[0].clone(),bv1.clone(),bv0.clone())?;
                            let rrhs = em.ite(rhs[0].clone(),bv1,bv0)?;
                            arr.push(em.bvadd(rlhs,rrhs)?);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    },
                    BitVecValue::BitVecValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let bv0 = em.const_bitvec(sz1,BigUint::from(0 as u8))?;
                            let bv1 = em.const_bitvec(sz1,BigUint::from(1 as u8))?;
                            let rlhs = em.ite(lhs[0].clone(),bv1,bv0)?;
                            arr.push(em.bvadd(rlhs,rhs[0].clone())?);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    }
                },
                BitVecValue::BitVecValue(sz1) => match *rhs {
                    BitVecValue::BoolValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let bv0 = em.const_bitvec(sz1,BigUint::from(0 as u8))?;
                            let bv1 = em.const_bitvec(sz1,BigUint::from(1 as u8))?;
                            let rrhs = em.ite(rhs[0].clone(),bv1,bv0)?;
                            arr.push(em.bvadd(lhs[0].clone(),rrhs)?);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    },
                    BitVecValue::BitVecValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            arr.push(em.bvadd(lhs[0].clone(),rhs[0].clone())?);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    }
                }
            },
            &llvm_ir::BinOp::Sub(_,_) => match *lhs {
                BitVecValue::BoolValue(sz1) => match *rhs {
                    BitVecValue::BoolValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let bv0 = em.const_bitvec(sz1,BigUint::from(0 as u8))?;
                            let bv1 = em.const_bitvec(sz1,BigUint::from(1 as u8))?;
                            let rlhs = em.ite(lhs[0].clone(),bv1.clone(),bv0.clone())?;
                            let rrhs = em.ite(rhs[0].clone(),bv1,bv0)?;
                            arr.push(em.bvsub(rlhs,rrhs)?);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    },
                    BitVecValue::BitVecValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let bv0 = em.const_bitvec(sz1,BigUint::from(0 as u8))?;
                            let bv1 = em.const_bitvec(sz1,BigUint::from(1 as u8))?;
                            let rlhs = em.ite(lhs[0].clone(),bv1,bv0)?;
                            arr.push(em.bvsub(rlhs,rhs[0].clone())?);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    }
                },
                BitVecValue::BitVecValue(sz1) => match *rhs {
                    BitVecValue::BoolValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let bv0 = em.const_bitvec(sz1,BigUint::from(0 as u8))?;
                            let bv1 = em.const_bitvec(sz1,BigUint::from(1 as u8))?;
                            let rrhs = em.ite(rhs[0].clone(),bv1,bv0)?;
                            arr.push(em.bvsub(lhs[0].clone(),rrhs)?);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    },
                    BitVecValue::BitVecValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            arr.push(em.bvsub(lhs[0].clone(),rhs[0].clone())?);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    }
                }
            },
            &llvm_ir::BinOp::Mul(_,_) => match *lhs {
                BitVecValue::BoolValue(sz1) => match *rhs {
                    BitVecValue::BoolValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            arr.push(em.or(vec![lhs[0].clone(),rhs[0].clone()])?);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    },
                    BitVecValue::BitVecValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let bv0 = em.const_bitvec(sz1,BigUint::from(0 as u8))?;
                            arr.push(em.ite(lhs[0].clone(),rhs[0].clone(),bv0)?);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    }
                },
                BitVecValue::BitVecValue(sz1) => match *rhs {
                    BitVecValue::BoolValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let bv0 = em.const_bitvec(sz1,BigUint::from(0 as u8))?;
                            arr.push(em.ite(rhs[0].clone(),lhs[0].clone(),bv0)?);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    },
                    BitVecValue::BitVecValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            arr.push(em.bvmul(lhs[0].clone(),rhs[0].clone())?);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    }
                }
            },
            &llvm_ir::BinOp::XOr => match *lhs {
                BitVecValue::BoolValue(sz1) => match *rhs {
                    BitVecValue::BoolValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            arr.push(em.xor(vec![lhs[0].clone(),rhs[0].clone()])?);
                            Ok(())
                        };
                        Ok((BitVecValue::BoolValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    },
                    BitVecValue::BitVecValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let bv0 = em.const_bitvec(sz1,BigUint::from(0 as u8))?;
                            let bv1 = em.const_bitvec(sz1,BigUint::from(1 as u8))?;
                            let nlhs = em.ite(lhs[0].clone(),bv1,bv0)?;
                            let res = em.bvxor(nlhs,rhs[0].clone())?;
                            arr.push(res);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    }
                },
                BitVecValue::BitVecValue(sz1) => match *rhs {
                    BitVecValue::BoolValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let bv0 = em.const_bitvec(sz1,BigUint::from(0 as u8))?;
                            let bv1 = em.const_bitvec(sz1,BigUint::from(1 as u8))?;
                            let nrhs = em.ite(rhs[0].clone(),bv1,bv0)?;
                            let res = em.bvxor(lhs[0].clone(),nrhs)?;
                            arr.push(res);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    },
                    BitVecValue::BitVecValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            arr.push(em.bvxor(lhs[0].clone(),rhs[0].clone())?);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    }
                }
            },
            &llvm_ir::BinOp::AShr => match *lhs {
                BitVecValue::BoolValue(sz1) => match *rhs {
                    BitVecValue::BoolValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let nr = em.not(rhs[0].clone())?;
                            let res = em.and(vec![nr,
                                                  lhs[0].clone()])?;
                            arr.push(res);
                            Ok(())
                        };
                        Ok((BitVecValue::BoolValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    },
                    BitVecValue::BitVecValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let bv0 = em.const_bitvec(sz1,BigUint::from(0 as u8))?;
                            let bv1 = em.const_bitvec(sz1,BigUint::from(1 as u8))?;
                            let nlhs = em.ite(lhs[0].clone(),bv1,bv0)?;
                            let res = em.bvashr(nlhs,rhs[0].clone())?;
                            arr.push(res);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    }
                },
                BitVecValue::BitVecValue(sz1) => match *rhs {
                    BitVecValue::BoolValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let bv0 = em.const_bitvec(sz1,BigUint::from(0 as u8))?;
                            let bv1 = em.const_bitvec(sz1,BigUint::from(1 as u8))?;
                            let nrhs = em.ite(rhs[0].clone(),bv1,bv0)?;
                            let res = em.bvashr(lhs[0].clone(),nrhs)?;
                            arr.push(res);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    },
                    BitVecValue::BitVecValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            arr.push(em.bvashr(lhs[0].clone(),rhs[0].clone())?);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    }
                }
            },
            &llvm_ir::BinOp::LShr => match *lhs {
                BitVecValue::BoolValue(sz1) => match *rhs {
                    BitVecValue::BoolValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let nr = em.not(rhs[0].clone())?;
                            let res = em.and(vec![nr,
                                                  lhs[0].clone()])?;
                            arr.push(res);
                            Ok(())
                        };
                        Ok((BitVecValue::BoolValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    },
                    BitVecValue::BitVecValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let bv0 = em.const_bitvec(sz1,BigUint::from(0 as u8))?;
                            let bv1 = em.const_bitvec(sz1,BigUint::from(1 as u8))?;
                            let nlhs = em.ite(lhs[0].clone(),bv1,bv0)?;
                            let res = em.bvlshr(nlhs,rhs[0].clone())?;
                            arr.push(res);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    }
                },
                BitVecValue::BitVecValue(sz1) => match *rhs {
                    BitVecValue::BoolValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let bv0 = em.const_bitvec(sz1,BigUint::from(0 as u8))?;
                            let bv1 = em.const_bitvec(sz1,BigUint::from(1 as u8))?;
                            let nrhs = em.ite(rhs[0].clone(),bv1,bv0)?;
                            let res = em.bvlshr(lhs[0].clone(),nrhs)?;
                            arr.push(res);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    },
                    BitVecValue::BitVecValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            arr.push(em.bvlshr(lhs[0].clone(),rhs[0].clone())?);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    }
                }
            },
            &llvm_ir::BinOp::SDiv(_) => match *lhs {
                BitVecValue::BoolValue(sz1) => match *rhs {
                    BitVecValue::BoolValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        Ok((BitVecValue::BoolValue(sz1),
                            inp_l))
                    },
                    BitVecValue::BitVecValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let bv0 = em.const_bitvec(sz1,BigUint::from(0 as u8))?;
                            let bv1 = em.const_bitvec(sz1,BigUint::from(1 as u8))?;
                            let nlhs = em.ite(lhs[0].clone(),bv1,bv0)?;
                            let res = em.bvsdiv(nlhs,rhs[0].clone())?;
                            arr.push(res);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    }
                },
                BitVecValue::BitVecValue(sz1) => match *rhs {
                    BitVecValue::BoolValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let bv0 = em.const_bitvec(sz1,BigUint::from(0 as u8))?;
                            let bv1 = em.const_bitvec(sz1,BigUint::from(1 as u8))?;
                            let nrhs = em.ite(rhs[0].clone(),bv1,bv0)?;
                            let res = em.bvsdiv(lhs[0].clone(),nrhs)?;
                            arr.push(res);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    },
                    BitVecValue::BitVecValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            arr.push(em.bvsdiv(lhs[0].clone(),rhs[0].clone())?);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    }
                }
            },
            &llvm_ir::BinOp::And => match *lhs {
                BitVecValue::BoolValue(sz1) => match *rhs {
                    BitVecValue::BoolValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let res = em.and(vec![lhs[0].clone(),
                                                  rhs[0].clone()])?;
                            arr.push(res);
                            Ok(())
                        };
                        Ok((BitVecValue::BoolValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    },
                    BitVecValue::BitVecValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let bv0 = em.const_bitvec(sz1,BigUint::from(0 as u8))?;
                            let bv1 = em.const_bitvec(sz1,BigUint::from(1 as u8))?;
                            let nlhs = em.ite(lhs[0].clone(),bv1,bv0)?;
                            let res = em.bvand(nlhs,rhs[0].clone())?;
                            arr.push(res);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    }
                },
                BitVecValue::BitVecValue(sz1) => match *rhs {
                    BitVecValue::BoolValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let bv0 = em.const_bitvec(sz1,BigUint::from(0 as u8))?;
                            let bv1 = em.const_bitvec(sz1,BigUint::from(1 as u8))?;
                            let nrhs = em.ite(rhs[0].clone(),bv1,bv0)?;
                            let res = em.bvand(lhs[0].clone(),nrhs)?;
                            arr.push(res);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    },
                    BitVecValue::BitVecValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            arr.push(em.bvand(lhs[0].clone(),rhs[0].clone())?);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    }
                }
            },
            &llvm_ir::BinOp::Or => match *lhs {
                BitVecValue::BoolValue(sz1) => match *rhs {
                    BitVecValue::BoolValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let res = em.or(vec![lhs[0].clone(),
                                                 rhs[0].clone()])?;
                            arr.push(res);
                            Ok(())
                        };
                        Ok((BitVecValue::BoolValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    },
                    BitVecValue::BitVecValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let bv0 = em.const_bitvec(sz1,BigUint::from(0 as u8))?;
                            let bv1 = em.const_bitvec(sz1,BigUint::from(1 as u8))?;
                            let nlhs = em.ite(lhs[0].clone(),bv1,bv0)?;
                            let res = em.bvor(nlhs,rhs[0].clone())?;
                            arr.push(res);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    }
                },
                BitVecValue::BitVecValue(sz1) => match *rhs {
                    BitVecValue::BoolValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let bv0 = em.const_bitvec(sz1,BigUint::from(0 as u8))?;
                            let bv1 = em.const_bitvec(sz1,BigUint::from(1 as u8))?;
                            let nrhs = em.ite(rhs[0].clone(),bv1,bv0)?;
                            let res = em.bvor(lhs[0].clone(),nrhs)?;
                            arr.push(res);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    },
                    BitVecValue::BitVecValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            arr.push(em.bvor(lhs[0].clone(),rhs[0].clone())?);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    }
                }
            },
            &llvm_ir::BinOp::Shl => match *lhs {
                BitVecValue::BoolValue(sz1) => match *rhs {
                    BitVecValue::BoolValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let bv0 = em.const_bitvec(sz1,BigUint::from(0 as u8))?;
                            let bv1 = em.const_bitvec(sz1,BigUint::from(1 as u8))?;
                            let rl = em.ite(lhs[0].clone(),bv1.clone(),bv0.clone())?;
                            let rr = em.ite(rhs[0].clone(),bv1.clone(),bv0.clone())?;
                            let res = em.bvshl(rl,rr)?;
                            arr.push(res);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    },
                    BitVecValue::BitVecValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let bv0 = em.const_bitvec(sz1,BigUint::from(0 as u8))?;
                            let bv1 = em.const_bitvec(sz1,BigUint::from(1 as u8))?;
                            let nlhs = em.ite(lhs[0].clone(),bv1,bv0)?;
                            let res = em.bvshl(nlhs,rhs[0].clone())?;
                            arr.push(res);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    }
                },
                BitVecValue::BitVecValue(sz1) => match *rhs {
                    BitVecValue::BoolValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            let bv0 = em.const_bitvec(sz1,BigUint::from(0 as u8))?;
                            let bv1 = em.const_bitvec(sz1,BigUint::from(1 as u8))?;
                            let nrhs = em.ite(rhs[0].clone(),bv1,bv0)?;
                            let res = em.bvshl(lhs[0].clone(),nrhs)?;
                            arr.push(res);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    },
                    BitVecValue::BitVecValue(sz2) => {
                        assert_eq!(sz1,sz2);
                        let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                            arr.push(em.bvshl(lhs[0].clone(),rhs[0].clone())?);
                            Ok(())
                        };
                        Ok((BitVecValue::BitVecValue(sz1),
                            Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                    }
                }
            },
            _ => panic!("BinOp: {:?}",op)
        }
    }
    fn sext<'a,Em>(val: OptRef<'a,Self>,inp: Transf<Em>,sz: usize,em: &mut Em)
                   -> (OptRef<'a,Self>,Transf<Em>)
        where Em : Embed {
        match val.as_ref() {
            &BitVecValue::BoolValue(_)
                => (OptRef::Owned(BitVecValue::BoolValue(sz)),inp),
            &BitVecValue::BitVecValue(bw) => {
                let ninp = Transformation::map_by_elem(Box::new(
                    move |_,_,e: Em::Expr,em: &mut Em| {
                        let bv0  = em.const_bitvec(bw,BigUint::from(0 as u8))?;
                        let sign = em.extract(bw-1,1,e.clone())?;
                        let rest = em.extract(0,bw-1,e.clone())?;
                        let pad0 = em.const_bitvec(sz-bw,BigUint::from(0 as u8))?;
                        let pad1 = em.const_bitvec(sz-bw,BigUint::from(1 as u8).shl(sz-bw)-(1 as u8))?;
                        let pad_cond = em.bvsge(e,bv0)?;
                        let pad  = em.ite(pad_cond,pad0,pad1)?;
                        let res1 = em.concat(sign,pad)?;
                        let res2 = em.concat(res1,rest)?;
                        Ok(res2)
                    }),inp);
                (OptRef::Owned(BitVecValue::BitVecValue(sz)),ninp)
            }
        }
    }
    fn zext<'a,Em>(val: OptRef<'a,Self>,inp: Transf<Em>,sz: usize,em: &mut Em)
                   -> (OptRef<'a,Self>,Transf<Em>)
        where Em : Embed {
        match val.as_ref() {
            &BitVecValue::BoolValue(_)
                => (OptRef::Owned(BitVecValue::BoolValue(sz)),inp),
            &BitVecValue::BitVecValue(bw) => {
                let ninp = Transformation::map_by_elem(Box::new(
                    move |_,_,e: Em::Expr,em: &mut Em| {
                        let pad = em.const_bitvec(sz-bw,BigUint::from(0 as u8))?;
                        Ok(em.concat(pad,e)?)
                    }),inp);
                (OptRef::Owned(BitVecValue::BitVecValue(sz)),ninp)
            }
        }
    }
    fn trunc<'a,Em>(val: OptRef<'a,Self>,inp: Transf<Em>,sz: usize,em: &mut Em)
                   -> (OptRef<'a,Self>,Transf<Em>)
        where Em : Embed {
        match val.as_ref() {
            &BitVecValue::BoolValue(_)
                => (OptRef::Owned(BitVecValue::BoolValue(sz)),inp),
            &BitVecValue::BitVecValue(bw) => {
                let ninp = Transformation::map_by_elem(Box::new(
                    move |_,_,e: Em::Expr,em: &mut Em| {
                        em.extract(0,sz,e)
                    }),inp);
                (OptRef::Owned(BitVecValue::BitVecValue(sz)),ninp)
            }
        }
    }
    fn icmp<Em>(op: &llvm_ir::CmpOp,
                lhs: &Self,lhs_inp: Transf<Em>,
                rhs: &Self,rhs_inp: Transf<Em>,
                em: &mut Em)
                -> Result<Transf<Em>,Em::Error>
        where Em : Embed {
        match lhs {
            &BitVecValue::BoolValue(_) => match rhs {
                &BitVecValue::BoolValue(_) => {
                    let f : Box<for <'b,'c> Fn(&'b [Em::Expr], &'c mut Em) -> Result<Em::Expr, Em::Error>> = match op {
                        &llvm_ir::CmpOp::Eq => Box::new(|es: &[Em::Expr],em: &mut Em| {
                            em.eq(es[0].clone(),es[1].clone())
                        }),
                        &llvm_ir::CmpOp::Ne => Box::new(|es: &[Em::Expr],em: &mut Em| {
                            let eq = em.eq(es[0].clone(),es[1].clone())?;
                            em.not(eq)
                        }),
                        &llvm_ir::CmpOp::SGe |
                        &llvm_ir::CmpOp::UGe => Box::new(|es: &[Em::Expr],em: &mut Em| {
                            let n = em.not(es[1].clone())?;
                            em.or(vec![es[0].clone(),n])
                        }),
                        &llvm_ir::CmpOp::SGt |
                        &llvm_ir::CmpOp::UGt => Box::new(|es: &[Em::Expr],em: &mut Em| {
                            let n = em.not(es[1].clone())?;
                            em.and(vec![es[0].clone(),n])
                        }),
                        &llvm_ir::CmpOp::SLt |
                        &llvm_ir::CmpOp::ULt => Box::new(|es: &[Em::Expr],em: &mut Em| {
                            let n = em.not(es[0].clone())?;
                            em.and(vec![n,es[1].clone()])
                        }),
                        _ => panic!("ICmp {:?} not implemented",op)
                    };
                    Ok(Transformation::zips_by_elem(f,vec![lhs_inp,rhs_inp]))
                },
                &BitVecValue::BitVecValue(bw) => {
                    let f : Box<for <'b,'c> Fn(&'b [Em::Expr], &'c mut Em) -> Result<Em::Expr, Em::Error>> = match op {
                        &llvm_ir::CmpOp::Eq => Box::new(move |es: &[Em::Expr],em: &mut Em| {
                            let one = em.const_bitvec(bw,BigUint::from(1 as u8))?;
                            let zero = em.const_bitvec(bw,BigUint::from(0 as u8))?;
                            let l = em.ite(es[0].clone(),one,zero)?;
                            em.eq(l,es[1].clone())
                        }),
                        &llvm_ir::CmpOp::Ne => Box::new(move |es: &[Em::Expr],em: &mut Em| {
                            let one = em.const_bitvec(bw,BigUint::from(1 as u8))?;
                            let zero = em.const_bitvec(bw,BigUint::from(0 as u8))?;
                            let l = em.ite(es[0].clone(),one,zero)?;
                            let eq = em.eq(l,es[1].clone())?;
                            em.not(eq)
                        }),
                        &llvm_ir::CmpOp::SGe => Box::new(move |es: &[Em::Expr],em: &mut Em| {
                            let one = em.const_bitvec(bw,BigUint::from(1 as u8))?;
                            let zero = em.const_bitvec(bw,BigUint::from(0 as u8))?;
                            let l = em.ite(es[0].clone(),one,zero)?;
                            em.bvsge(l,es[1].clone())
                        }),
                        &llvm_ir::CmpOp::SLt => Box::new(move |es: &[Em::Expr],em: &mut Em| {
                            let one = em.const_bitvec(bw,BigUint::from(1 as u8))?;
                            let zero = em.const_bitvec(bw,BigUint::from(0 as u8))?;
                            let l = em.ite(es[0].clone(),one,zero)?;
                            em.bvslt(l,es[1].clone())
                        }),
                        &llvm_ir::CmpOp::SLe => Box::new(move |es: &[Em::Expr],em: &mut Em| {
                            let one = em.const_bitvec(bw,BigUint::from(1 as u8))?;
                            let zero = em.const_bitvec(bw,BigUint::from(0 as u8))?;
                            let l = em.ite(es[0].clone(),one,zero)?;
                            em.bvsle(l,es[1].clone())
                        }),
                        _ => panic!("ICmp {:?} not implemented",op)
                    };
                    Ok(Transformation::zips_by_elem(f,vec![lhs_inp,rhs_inp]))
                }
            },
            &BitVecValue::BitVecValue(bwl) => match rhs {
                &BitVecValue::BitVecValue(bwr) => {
                    debug_assert_eq!(bwl,bwr);
                    let f : Box<for <'b,'c> Fn(&'b [Em::Expr], &'c mut Em) -> Result<Em::Expr, Em::Error>> = match op {
                        &llvm_ir::CmpOp::Eq => Box::new(|es: &[Em::Expr],em: &mut Em| {
                            em.eq(es[0].clone(),es[1].clone())
                        }),
                        &llvm_ir::CmpOp::Ne => Box::new(|es: &[Em::Expr],em: &mut Em| {
                            let eq = em.eq(es[0].clone(),es[1].clone())?;
                            em.not(eq)
                        }),
                        &llvm_ir::CmpOp::SGe => Box::new(|es: &[Em::Expr],em: &mut Em| {
                            em.bvsge(es[0].clone(),es[1].clone())
                        }),
                        &llvm_ir::CmpOp::SGt => Box::new(|es: &[Em::Expr],em: &mut Em| {
                            em.bvsgt(es[0].clone(),es[1].clone())
                        }),
                        &llvm_ir::CmpOp::SLe => Box::new(|es: &[Em::Expr],em: &mut Em| {
                            em.bvsle(es[0].clone(),es[1].clone())
                        }),
                        &llvm_ir::CmpOp::SLt => Box::new(|es: &[Em::Expr],em: &mut Em| {
                            em.bvslt(es[0].clone(),es[1].clone())
                        }),
                        _ => panic!("ICmp {:?} not implemented",op)
                    };
                    Ok(Transformation::zips_by_elem(f,vec![lhs_inp,rhs_inp]))
                },
                &BitVecValue::BoolValue(bwr) => {
                    debug_assert_eq!(bwl,bwr);
                    let f : Box<for <'b,'c> Fn(&'b [Em::Expr], &'c mut Em) -> Result<Em::Expr, Em::Error>> = match op {
                        &llvm_ir::CmpOp::Eq => Box::new(move |es: &[Em::Expr],em: &mut Em| {
                            let one = em.const_bitvec(bwl,BigUint::from(1 as u8))?;
                            let zero = em.const_bitvec(bwl,BigUint::from(0 as u8))?;
                            let r = em.ite(es[1].clone(),one,zero)?;
                            em.eq(es[0].clone(),r)
                        }),
                        &llvm_ir::CmpOp::Ne => Box::new(move |es: &[Em::Expr],em: &mut Em| {
                            let one = em.const_bitvec(bwl,BigUint::from(1 as u8))?;
                            let zero = em.const_bitvec(bwl,BigUint::from(0 as u8))?;
                            let r = em.ite(es[1].clone(),one,zero)?;
                            let eq = em.eq(es[0].clone(),r)?;
                            em.not(eq)
                        }),
                        &llvm_ir::CmpOp::SGe => Box::new(move |es: &[Em::Expr],em: &mut Em| {
                            let one = em.const_bitvec(bwl,BigUint::from(1 as u8))?;
                            let zero = em.const_bitvec(bwl,BigUint::from(0 as u8))?;
                            let r = em.ite(es[1].clone(),one,zero)?;
                            em.bvsge(es[0].clone(),r)
                        }),
                        &llvm_ir::CmpOp::SGt => Box::new(move |es: &[Em::Expr],em: &mut Em| {
                            let one = em.const_bitvec(bwl,BigUint::from(1 as u8))?;
                            let zero = em.const_bitvec(bwl,BigUint::from(0 as u8))?;
                            let r = em.ite(es[1].clone(),one,zero)?;
                            em.bvsgt(es[0].clone(),r)
                        }),
                        _ => panic!("ICmp {:?} not implemented",op)
                    };
                    Ok(Transformation::zips_by_elem(f,vec![lhs_inp,rhs_inp]))
                }
            }
        }
    }
    fn from_bool<Em : Embed>(v: Transf<Em>) -> Result<(Self,Transf<Em>),Em::Error> {
        Ok((BitVecValue::BoolValue(1),v))
    }
    fn to_bool<'a,Em : Embed>(val: OptRef<'a,Self>,inp: Transf<Em>) -> Result<Transf<Em>,Em::Error> {
        match val.as_ref() {
            &BitVecValue::BoolValue(_) => Ok(inp),
            &BitVecValue::BitVecValue(bw) => {
                let f = move |_:&[Em::Expr],_:usize,e: Em::Expr,em: &mut Em| {
                    let zero = em.const_bitvec(bw,BigUint::from(0 as u8))?;
                    let eq = em.eq(e,zero)?;
                    em.not(eq)
                };
                let r = Transformation::map_by_elem(Box::new(f),inp);
                Ok(r)
            }
        }
    }
}

impl Bytes for BitVecValue {
    fn byte_width(&self) -> usize {
        match self {
            &BitVecValue::BoolValue(sz) => sz/8,
            &BitVecValue::BitVecValue(sz) => sz/8
        }
    }
    fn extract_bytes<'a,Em : Embed>(v: OptRef<'a,Self>,inp_v: Transf<Em>,start: usize,len: usize,em: &mut Em)
                                    -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error> {
        match v.as_ref() {
            &BitVecValue::BoolValue(sz) => {
                let rsz = sz/8;
                if start+len==rsz {
                    Ok(Some((OptRef::Owned(BitVecValue::BoolValue(len*8)),inp_v)))
                } else {
                    let ninp = Transformation::const_bool(false,em)?;
                    Ok(Some((OptRef::Owned(BitVecValue::BoolValue(len*8)),ninp)))
                }
            },
            &BitVecValue::BitVecValue(_) => {
                //let rsz = sz/8;
                unimplemented!()
                //let ninp = Transformation::map_by_elem(Box::new(|_,_,e,em| { em.
            }
        }
    }
}

/*impl<Ptr,V> CompValue<Ptr,V> {
    pub fn lower<'a>(x: OptRef<'a,Self>) -> CompValue<OptRef<'a,BitField<Ptr>>,OptRef<'a,V>> {
        match x {
            OptRef::Owned(CompValue::Value(v))
                => CompValue::Value(OptRef::Owned(v)),
            OptRef::Owned(CompValue::Pointer(p))
                => CompValue::Pointer(OptRef::Owned(p)),
            OptRef::Owned(CompValue::Vector(mut v))
                => CompValue::Vector(v.drain(..).map(|x| CompValue::lower(OptRef::Owned(x))).collect()),
            OptRef::Ref(&CompValue::Value(ref v))
                => CompValue::Value(OptRef::Ref(v)),
            OptRef::Ref(&CompValue::Pointer(ref p))
                => CompValue::Pointer(OptRef::Ref(p)),
            OptRef::Ref(&CompValue::Vector(ref v))
                => CompValue::Vector(v.iter().map(|x| CompValue::lower(OptRef::Ref(x))).collect()),
        }
    }
}*/

impl<Ptr : Composite+Clone,V : Composite+Clone> Composite for CompValue<Ptr,V> {
    fn num_elem(&self) -> usize {
        match self {
            &CompValue::Value(ref v) => v.num_elem(),
            &CompValue::Pointer(ref p) => p.num_elem(),
            &CompValue::Vector(ref v) => v.num_elem()
        }
    }
    fn elem_sort<Em : Embed>(&self,n:usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        match self {
            &CompValue::Value(ref v) => v.elem_sort(n,em),
            &CompValue::Pointer(ref p) => p.elem_sort(n,em),
            &CompValue::Vector(ref v) => v.elem_sort(n,em)
        }
    }
    fn combine<'a,Em,FComb,FL,FR>(x: OptRef<'a,Self>,y: OptRef<'a,Self>,
                                  inp_x: Transf<Em>,inp_y: Transf<Em>,
                                  comb: &FComb,only_l:&FL,only_r:&FR,em: &mut Em)
                                  -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>
        where Em : Embed,
              FComb : Fn(Transf<Em>,Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FL : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FR : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error> {

        match x {
            OptRef::Ref(&CompValue::Value(ref vx)) => {
                let rvx = OptRef::Ref(vx);
                let rvy = match y {
                    OptRef::Ref(&CompValue::Value(ref vy))
                        => OptRef::Ref(vy),
                    OptRef::Owned(CompValue::Value(vy))
                        => OptRef::Owned(vy),
                    _ => return Ok(None)
                };
                match V::combine(rvx,rvy,inp_x,inp_y,
                                 comb,only_l,only_r,em)? {
                    None => Ok(None),
                    Some((nv,inp_nv)) => Ok(Some((OptRef::Owned(CompValue::Value(nv.as_obj())),inp_nv)))
                }
            },
            OptRef::Owned(CompValue::Value(vx)) => {
                let rvx = OptRef::Owned(vx);
                let rvy = match y {
                    OptRef::Ref(&CompValue::Value(ref vy))
                        => OptRef::Ref(vy),
                    OptRef::Owned(CompValue::Value(vy))
                        => OptRef::Owned(vy),
                    _ => return Ok(None)
                };
                match V::combine(rvx,rvy,inp_x,inp_y,
                                 comb,only_l,only_r,em)? {
                    None => Ok(None),
                    Some((nv,inp_nv)) => Ok(Some((OptRef::Owned(CompValue::Value(nv.as_obj())),inp_nv)))
                }
            },
            OptRef::Ref(&CompValue::Pointer(ref vx)) => {
                let rvx = OptRef::Ref(vx);
                let rvy = match y {
                    OptRef::Ref(&CompValue::Pointer(ref vy))
                        => OptRef::Ref(vy),
                    OptRef::Owned(CompValue::Pointer(vy))
                        => OptRef::Owned(vy),
                    _ => return Ok(None)
                };
                match BitField::combine(rvx,rvy,inp_x,inp_y,
                                        comb,only_l,only_r,em)? {
                    None => Ok(None),
                    Some((nv,inp_nv)) => Ok(Some((OptRef::Owned(CompValue::Pointer(nv.as_obj())),inp_nv)))
                }
            },
            OptRef::Owned(CompValue::Pointer(vx)) => {
                let rvx = OptRef::Owned(vx);
                let rvy = match y {
                    OptRef::Ref(&CompValue::Pointer(ref vy))
                        => OptRef::Ref(vy),
                    OptRef::Owned(CompValue::Pointer(vy))
                        => OptRef::Owned(vy),
                    _ => return Ok(None)
                };
                match BitField::combine(rvx,rvy,inp_x,inp_y,
                                        comb,only_l,only_r,em)? {
                    None => Ok(None),
                    Some((nv,inp_nv)) => Ok(Some((OptRef::Owned(CompValue::Pointer(nv.as_obj())),inp_nv)))
                }
            },
            OptRef::Ref(&CompValue::Vector(ref vx)) => {
                let rvx = OptRef::Ref(vx);
                let rvy = match y {
                    OptRef::Ref(&CompValue::Vector(ref vy))
                        => OptRef::Ref(vy),
                    OptRef::Owned(CompValue::Vector(vy))
                        => OptRef::Owned(vy),
                    _ => return Ok(None)
                };
                match Vec::combine(rvx,rvy,inp_x,inp_y,
                                   comb,only_l,only_r,em)? {
                    None => Ok(None),
                    Some((nv,inp_nv)) => Ok(Some((OptRef::Owned(CompValue::Vector(nv.as_obj())),inp_nv)))
                }
            },
            OptRef::Owned(CompValue::Vector(vx)) => {
                let rvx = OptRef::Owned(vx);
                let rvy = match y {
                    OptRef::Ref(&CompValue::Vector(ref vy))
                        => OptRef::Ref(vy),
                    OptRef::Owned(CompValue::Vector(vy))
                        => OptRef::Owned(vy),
                    _ => return Ok(None)
                };
                match Vec::combine(rvx,rvy,inp_x,inp_y,
                                   comb,only_l,only_r,em)? {
                    None => Ok(None),
                    Some((nv,inp_nv)) => Ok(Some((OptRef::Owned(CompValue::Vector(nv.as_obj())),inp_nv)))
                }
            }
        }
    }
}

impl<'c,Ptr : Pointer<'c>+Bytes+Clone,V : IntValue+Bytes+Clone> IntValue for CompValue<Ptr,V> {
    fn to_offset<'a,Em : Embed>(v: OptRef<'a,Self>,tr: Transf<Em>) -> (Singleton,Transf<Em>) {
        match v {
            OptRef::Owned(CompValue::Value(pv))
                => V::to_offset(OptRef::Owned(pv),tr),
            OptRef::Ref(&CompValue::Value(ref pv))
                => V::to_offset(OptRef::Ref(pv),tr),
            _ => panic!("Pointer cannot be used as offset")
        }
    }
    fn from_offset<'a,Em : Embed>(bw: usize,tp: &Singleton,inp: Transf<Em>)
                                  -> (Self,Transf<Em>) {
        let (v,v_inp) = V::from_offset(bw,tp,inp);
        (CompValue::Value(v),v_inp)
    }

    fn const_int<Em : Embed>(bw: u64,val: BigUint,em: &mut Em) -> Result<(Self,Vec<Em::Expr>),Em::Error> {
        let (v,inp_v) = V::const_int(bw,val,em)?;
        Ok((CompValue::Value(v),inp_v))
    }
    fn bin<'b,Em>(op: &llvm_ir::BinOp,
                  lhs: &Self,
                  rhs: &Self,
                  inp_l: Transf<Em>,
                  inp_r: Transf<Em>,
                  exprs: &[Em::Expr],
                  em: &mut Em)
                  -> Result<(Self,Transf<Em>),Em::Error>
        where Em : DeriveValues {
        match lhs {
            &CompValue::Value(ref rlhs) => {
                let rrhs = match rhs {
                    &CompValue::Value(ref v)
                        => v,
                    _ => panic!("Cannot binop pointers with values")
                };
                let (res,inp_res) = V::bin(op,rlhs,rrhs,inp_l,inp_r,exprs,em)?;
                Ok((CompValue::Value(res),
                    inp_res))
            },
            &CompValue::Pointer(ref rlhs) => match op {
                &llvm_ir::BinOp::And => match rhs {
                    &CompValue::Value(ref rrhs) => {
                        let (_,mask_inp) = V::to_offset(OptRef::Ref(rrhs),inp_r);
                        let mask_e = mask_inp.get(&exprs,0,em)?;
                        match em.derive_const(&mask_e)? {
                            None => unimplemented!(),
                            Some(mask_c) => if value_as_index(&mask_c)<8 {
                                let (res,inp_res) = V::const_int((rrhs.byte_width()*8) as u64,BigUint::from(0 as u8),em)?;
                                Ok((CompValue::Value(res),
                                    Transformation::constant(inp_res)))
                            } else {
                                unimplemented!()
                            }
                        }
                    },
                    _ => unimplemented!()
                },
                &llvm_ir::BinOp::Sub(_,_) => match rhs {
                    &CompValue::Pointer(ref rrhs) => {
                        let bw = rlhs.byte_width()*8;
                        let (l_base,l_base_inp) = BitField::to_pointer(
                            OptRef::Ref(rlhs),inp_l
                        ).unwrap();
                        let (r_base,r_base_inp) = BitField::to_pointer(
                            OptRef::Ref(rrhs),inp_r
                        ).unwrap();
                        let tp : SortKind<Sort> = SortKind::BitVec(bw);
                        let res_inp = ptr_sub(l_base.as_ref(),
                                              l_base_inp,
                                              r_base.as_ref(),
                                              r_base_inp,
                                              &tp,em)?;
                        let srt = Singleton(Sort::from_kind(tp));
                        let (ret,ret_inp) = V::from_offset(bw,&srt,res_inp);
                        Ok((CompValue::Value(ret),ret_inp))
                    },
                    _ => unimplemented!()
                },
                _ => unimplemented!()
            },
            &CompValue::Vector(_) => {
                unimplemented!()
            }
        }
    }
    fn sext<'a,Em>(x: OptRef<'a,Self>,inp: Transf<Em>,sz: usize,em: &mut Em)
                   -> (OptRef<'a,Self>,Transf<Em>)
        where Em : Embed {
        let (nx,ninp) = match x {
            OptRef::Owned(CompValue::Value(v)) => {
                let (nv,ninp) = V::sext(OptRef::Owned(v),inp,sz,em);
                (CompValue::Value(nv.as_obj()),ninp)
            },
            OptRef::Ref(&CompValue::Value(ref v)) => {
                let (nv,ninp) = V::sext(OptRef::Ref(v),inp,sz,em);
                (CompValue::Value(nv.as_obj()),ninp)
            },
            _ => panic!("Cannot sext pointers")
        };
        (OptRef::Owned(nx),ninp)
    }
    fn zext<'a,Em>(x: OptRef<'a,Self>,inp: Transf<Em>,sz: usize,em: &mut Em)
                   -> (OptRef<'a,Self>,Transf<Em>)
        where Em : Embed {
        let (nx,ninp) = match x {
            OptRef::Owned(CompValue::Value(v)) => {
                let (nv,ninp) = V::zext(OptRef::Owned(v),inp,sz,em);
                (CompValue::Value(nv.as_obj()),ninp)
            },
            OptRef::Ref(&CompValue::Value(ref v)) => {
                let (nv,ninp) = V::zext(OptRef::Ref(v),inp,sz,em);
                (CompValue::Value(nv.as_obj()),ninp)
            },
            _ => panic!("Cannot zext pointers")
        };
        (OptRef::Owned(nx),ninp)
    }
    fn trunc<'a,Em>(x: OptRef<'a,Self>,inp: Transf<Em>,sz: usize,em: &mut Em)
                    -> (OptRef<'a,Self>,Transf<Em>)
        where Em : Embed {
        let (nx,ninp) = match x {
            OptRef::Owned(CompValue::Value(v)) => {
                let (nv,ninp) = V::trunc(OptRef::Owned(v),inp,sz,em);
                (CompValue::Value(nv.as_obj()),ninp)
            },
            OptRef::Ref(&CompValue::Value(ref v)) => {
                let (nv,ninp) = V::trunc(OptRef::Ref(v),inp,sz,em);
                (CompValue::Value(nv.as_obj()),ninp)
            },
            _ => panic!("Cannot truncate pointers")
        };
        (OptRef::Owned(nx),ninp)
    }

    fn icmp<Em>(op: &llvm_ir::CmpOp,
                lhs: &Self,lhs_inp: Transf<Em>,
                rhs: &Self,rhs_inp: Transf<Em>,
                em: &mut Em)
                -> Result<Transf<Em>,Em::Error>
        where Em : Embed {

        match lhs {
            &CompValue::Value(ref vl) => match rhs {
                &CompValue::Value(ref vr)
                    => V::icmp(op,vl,lhs_inp,vr,rhs_inp,em),
                _ => panic!("Cannot compare values with pointers")
            },
            &CompValue::Pointer(ref pl) => match rhs {
                &CompValue::Pointer(ref pr)
                    => match op {
                        &llvm_ir::CmpOp::Eq => Ok(BitField::ptr_eq(pl,lhs_inp,
                                                                   pr,rhs_inp)),
                        &llvm_ir::CmpOp::Ne
                            => Ok(Transformation::not(BitField::ptr_eq(pl,lhs_inp,
                                                                       pr,rhs_inp))),
                        &llvm_ir::CmpOp::ULt => BitField::ptr_lt(pl,lhs_inp,
                                                                 pr,rhs_inp,em),
                        _ => panic!("Cannot compare pointers using {:?}",op)
                    },
                _ => panic!("Cannot compare values with pointers")
            },
            _ => panic!("Cannot icmp")
        }
    }
    fn from_bool<Em : Embed>(v: Transf<Em>) -> Result<(Self,Transf<Em>),Em::Error> {
        let (r,r_inp) = V::from_bool(v)?;
        Ok((CompValue::Value(r),r_inp))
    }
    fn to_bool<'a,Em : Embed>(val: OptRef<'a,Self>,inp: Transf<Em>) -> Result<Transf<Em>,Em::Error> {
        let rval = match val {
            OptRef::Owned(CompValue::Value(v))
                => OptRef::Owned(v),
            OptRef::Ref(&CompValue::Value(ref v))
                => OptRef::Ref(v),
            _ => panic!("Cannot convert pointers to bool")
        };
        V::to_bool(rval,inp)
    }
}

impl<Ptr : Bytes+Clone,V : Bytes+Clone> Bytes for CompValue<Ptr,V> {
    fn byte_width(&self) -> usize {
        match self {
            &CompValue::Value(ref v) => v.byte_width(),
            &CompValue::Pointer(ref p) => p.obj.byte_width(),
            &CompValue::Vector(ref v) => {
                let mut acc = 0;
                for el in v.iter() {
                    acc+=el.byte_width()
                }
                acc
            }
        }
    }
    fn extract_bytes<'a,Em : Embed>(x: OptRef<'a,Self>,
                                    inp_x: Transf<Em>,
                                    start: usize,
                                    len: usize,
                                    em: &mut Em)
                                    -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error> {
        match x {
            OptRef::Ref(&CompValue::Value(ref vx)) => match V::extract_bytes(OptRef::Ref(vx),inp_x,start,len,em)? {
                None => Ok(None),
                Some((nvx,inp_nvx)) => Ok(Some((OptRef::Owned(CompValue::Value(nvx.as_obj())),
                                                inp_nvx)))
            },
            OptRef::Owned(CompValue::Value(vx)) => match V::extract_bytes(OptRef::Owned(vx),inp_x,start,len,em)? {
                None => Ok(None),
                Some((nvx,inp_nvx)) => Ok(Some((OptRef::Owned(CompValue::Value(nvx.as_obj())),
                                                inp_nvx)))
            },
            OptRef::Ref(&CompValue::Pointer(ref vx)) => match BitField::extract_bytes(OptRef::Ref(vx),inp_x,start,len,em)? {
                None => Ok(None),
                Some((nvx,inp_nvx)) => Ok(Some((OptRef::Owned(CompValue::Pointer(nvx.as_obj())),
                                                inp_nvx)))
            },
            OptRef::Owned(CompValue::Pointer(vx)) => match BitField::extract_bytes(OptRef::Owned(vx),inp_x,start,len,em)? {
                None => Ok(None),
                Some((nvx,inp_nvx)) => Ok(Some((OptRef::Owned(CompValue::Pointer(nvx.as_obj())),
                                                inp_nvx)))
            },
            OptRef::Ref(&CompValue::Vector(ref vx)) => {
                let mut acc = 0;
                let mut off = 0;
                for el in vx.iter() {
                    let sz = el.byte_width();
                    let nel = el.num_elem();
                    if start >= acc {
                        if len + start - acc > sz {
                            return Ok(None)
                        } else {
                            return CompValue::extract_bytes(OptRef::Ref(el),
                                                            Transformation::view(off,nel,inp_x),
                                                            start-acc,len,em)
                        }
                    }
                    acc+=sz;
                    off+=nel;
                }
                Ok(None)
            },
            OptRef::Owned(CompValue::Vector(mut vx)) => {
                let mut acc = 0;
                let mut off = 0;
                for el in vx.drain(..) {
                    let sz = el.byte_width();
                    let nel = el.num_elem();
                    if start >= acc {
                        if len + start - acc > sz {
                            return Ok(None)
                        } else {
                            return CompValue::extract_bytes(OptRef::Owned(el),
                                                            Transformation::view(off,nel,inp_x),
                                                            start-acc,len,em)
                        }
                    }
                    acc+=sz;
                    off+=nel;
                }
                Ok(None)
            }
        }
    }
}

impl<'a,Ptr : Pointer<'a>+Clone,V : Composite+Clone> Pointer<'a> for CompValue<Ptr,V> {
    fn from_pointer<'b,Em : Embed>(bw: usize,
                                   base: OptRef<'b,BasePointer<'a>>,
                                   inp_base: Transf<Em>)
                                   -> (OptRef<'b,Self>,Transf<Em>) {
        let (ptr,inp_ptr) = BitField::from_pointer(bw,base,inp_base);
        (OptRef::Owned(CompValue::Pointer(ptr.as_obj())),inp_ptr)
    }
    fn to_pointer<'b,Em : Embed>(ptr: OptRef<'b,Self>,
                                 inp_ptr: Transf<Em>)
                                 -> Option<(OptRef<'b,BasePointer<'a>>,Transf<Em>)> {
        let rptr = match ptr {
            OptRef::Owned(CompValue::Pointer(p))
                => OptRef::Owned(p),
            OptRef::Ref(&CompValue::Pointer(ref p))
                => OptRef::Ref(p),
            _ => return None
        };
        BitField::to_pointer(rptr,inp_ptr)
    }
    fn ptr_eq<Em : Embed>(lhs: &Self,lhs_inp: Transf<Em>,
                          rhs: &Self,rhs_inp: Transf<Em>)
                          -> Transf<Em> {
        match lhs {
            &CompValue::Pointer(ref pl) => match rhs {
                &CompValue::Pointer(ref pr)
                    => BitField::ptr_eq(pl,lhs_inp,pr,rhs_inp),
                _ => panic!("Cannot eq pointers and values")
            },
            _ => panic!("Cannot eq pointers and values")
        }
    }
    fn ptr_lt<Em : Embed>(lhs: &Self,lhs_inp: Transf<Em>,
                          rhs: &Self,rhs_inp: Transf<Em>,em: &mut Em)
                          -> Result<Transf<Em>,Em::Error> {
        match lhs {
            &CompValue::Pointer(ref pl) => match rhs {
                &CompValue::Pointer(ref pr)
                    => BitField::ptr_lt(pl,lhs_inp,pr,rhs_inp,em),
                _ => panic!("Cannot compare pointers and values")
            },
            _ => panic!("Cannot compare pointers and values")
        }
    }

}

impl<C : Composite+Clone> Composite for ByteWidth<C> {
    fn num_elem(&self) -> usize {
        self.value.num_elem()
    }
    fn elem_sort<Em : Embed>(&self,n:usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        self.value.elem_sort(n,em)
    }
    fn combine<'a,Em,FComb,FL,FR>(x: OptRef<'a,Self>,y: OptRef<'a,Self>,
                                  inp_x: Transf<Em>,inp_y: Transf<Em>,
                                  comb: &FComb,only_l:&FL,only_r:&FR,em: &mut Em)
                                  -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>
        where Em : Embed,
              FComb : Fn(Transf<Em>,Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FL : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FR : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error> {
        let bw = x.as_ref().byte_width;
        if bw!=y.as_ref().byte_width {
            return Ok(None)
        }
        let rx = match x {
            OptRef::Owned(cx) => OptRef::Owned(cx.value),
            OptRef::Ref(ref cx) => OptRef::Ref(&cx.value)
        };
        let ry = match y {
            OptRef::Owned(cy) => OptRef::Owned(cy.value),
            OptRef::Ref(ref cy) => OptRef::Ref(&cy.value)
        };
        match C::combine(rx,ry,inp_x,inp_y,comb,only_l,only_r,em)? {
            None => Ok(None),
            Some((n,inp_n)) => Ok(Some((OptRef::Owned(ByteWidth { value: n.as_obj(),
                                                                  byte_width: bw }),
                                        inp_n)))
        }
    }
}

impl<'a,C : Pointer<'a>+Clone> Pointer<'a> for ByteWidth<C> {
    fn from_pointer<'b,Em : Embed>(bw: usize,
                                   base: OptRef<'b,BasePointer<'a>>,
                                   inp_base: Transf<Em>)
                                   -> (OptRef<'b,Self>,Transf<Em>) {
        let (val,inp_val) = C::from_pointer(bw,base,inp_base);
        (OptRef::Owned(ByteWidth { value: val.as_obj(),
                                   byte_width: bw }),inp_val)
    }
    fn to_pointer<'b,Em : Embed>(p: OptRef<'b,Self>,inp_p: Transf<Em>)
                                 -> Option<(OptRef<'b,BasePointer<'a>>,Transf<Em>)> {
        match p {
            OptRef::Owned(rp) => C::to_pointer(OptRef::Owned(rp.value),inp_p),
            OptRef::Ref(ref rp) => C::to_pointer(OptRef::Ref(&rp.value),inp_p)
        }
    }
    fn ptr_eq<Em : Embed>(lhs: &Self,lhs_inp: Transf<Em>,
                          rhs: &Self,rhs_inp: Transf<Em>)
                          -> Transf<Em> {
        C::ptr_eq(&lhs.value,lhs_inp,&rhs.value,rhs_inp)
    }
    fn ptr_lt<Em : Embed>(lhs: &Self,lhs_inp: Transf<Em>,
                          rhs: &Self,rhs_inp: Transf<Em>,em: &mut Em)
                          -> Result<Transf<Em>,Em::Error> {
        C::ptr_lt(&lhs.value,lhs_inp,&rhs.value,rhs_inp,em)
    }

}

impl<'a,C : Composite+Clone> Bytes for ByteWidth<C> {
    fn byte_width(&self) -> usize {
        self.byte_width
    }
    fn extract_bytes<'b,Em : Embed>(_:OptRef<'b,Self>,
                                    _:Transf<Em>,
                                    _:usize,
                                    _:usize,
                                    _:&mut Em)
                                    -> Result<Option<(OptRef<'b,Self>,Transf<Em>)>,Em::Error> {
        Ok(None)
    }

}

impl<Ptr : Composite+Clone,V : Composite+Clone> Vector for CompValue<Ptr,V> {
    fn vector<'a,Em : Embed>(vec: OptRef<'a,Vec<Self>>,
                             inp_vec: Vec<Transf<Em>>,
                             _: &mut Em)
                             -> Result<(OptRef<'a,Self>,Transf<Em>),Em::Error> {
        Ok((OptRef::Owned(CompValue::Vector(vec.as_obj())),
            Transformation::concat(&inp_vec)))
    }
}

impl<'a,Ptr : Bytes+Pointer<'a>+Clone,V : Bytes+IntValue+Clone> FromConst<'a> for CompValue<Ptr,V> {
    fn from_const<'b,Em : Embed>(dl: &'a DataLayout,
                                 c: &'a llvm_ir::Constant,
                                 tp: &'a Type,
                                 tps: &'a HashMap<String,Type>,
                                 em: &mut Em)
                                 -> Result<Option<(Self,Transf<Em>)>,Em::Error> {
        let res = translate_constant(dl,c,tp,tps,em)?;
        Ok(Some(res))
    }
}
