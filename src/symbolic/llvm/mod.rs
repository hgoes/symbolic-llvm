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

use self::smtrs::composite::*;
use self::smtrs::embed::{Embed,DeriveValues};
use self::smtrs::types::{Sort,SortKind};
use self::num_bigint::BigInt;
use self::num_traits::cast::ToPrimitive;
use std::fmt::Debug;
use std::collections::HashMap;
use self::mem::{Bytes,FromConst,MemSlice,MemObj};
use self::frame::*;
use self::thread::*;
use self::program::*;
use self::pointer::*;
use self::llvm_ir::Module;
use self::llvm_ir::datalayout::{DataLayout};
use self::llvm_ir::types::{Type};

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash,Copy,Clone,Debug)]
pub struct InstructionRef<'a> {
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
            basic_block: &fun.body.as_ref().expect("Function has no body")[0].name,
            instruction: 0
        }
    }
    pub fn resolve(&self,fun: &'a llvm_ir::Function) -> &'a llvm_ir::Instruction {
        &fun.body.as_ref().expect("Function has no body")
            .iter()
            .find(|bb| bb.name == *self.basic_block).expect("Cannot find basic block")
            .instrs[self.instruction]
    }
    pub fn next(&self) -> Self {
        InstructionRef { basic_block: self.basic_block,
                         instruction: self.instruction + 1 }
    }
}

const INDEX_WIDTH: usize = 32;

pub fn translate_init<'a,'b,V,Em>(module: &'a Module,
                                  entry_fun: &'a String,
                                  args: Vec<V>,
                                  inp_args: Transf<Em>,
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
                                                OptRef::Owned(Data(InstructionRef { basic_block: main_blk,
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
                                                  OptRef::Owned(None),
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
    
    Ok(program(threads,inp_threads,globals,inp_globals,heap,inp_heap))
}

fn filter_ctx_id<'a,V>(cf_id: &CallId<'a>,el: (ThreadView<'a,V>,&Data<Option<ContextId<'a>>>))
                       -> Option<(ThreadView<'a,V>,ContextId<'a>)> {
    match (el.1).0 {
        None => None,
        Some(ContextId::Call(cid)) => if cid==*cf_id { Some((el.0,ContextId::Call(cid))) } else { None },
        Some(ContextId::Stack(cid,instr)) => if cid==*cf_id { Some((el.0,ContextId::Stack(cid,instr))) } else { None }
    }
}

pub fn translate_instr<'b,V,Em
                       >(dl: &'b DataLayout,
                         tps: &'b HashMap<String,Type>,
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
                                    Transf<Em>),
                                   TrErr<'b,V,Em::Error>>
    where V : 'b+Bytes+FromConst<'b>+IntValue+Vector+Pointer<'b>+Debug,Em : DeriveValues {
    debug_assert_eq!(prog.num_elem(),prog_inp.size());
    debug_assert_eq!(inp.num_elem(),inp_inp.size());
    let (step,thr_idx) = if prog.is_single_threaded() {
        let idx = em.const_bitvec(STEP_BW,BigInt::from(0))?;
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
    let cur_thread_iter
        = CurrentThreadIter::new(prog,
                                 thread_id,
                                 step,
                                 thr_idx,
                                 exprs,
                                 em)?;
    let cur_frame_id = top_frame_id_iter(prog,prog_inp.clone(),cur_thread_iter)
        .filter(cf_id,filter_ctx_id);
    let cfs = cur_frame_id.clone().seq((prog,prog_inp.clone(),exprs),frame_id_to_call_frame_iter);
    let frs = cur_frame_id.seq((prog,prog_inp.clone(),exprs),frame_id_to_frame_iter);
    let mut ctxs = cfs.product(frs).cond_iter();
    match instr.content {
        llvm_ir::InstructionC::Alloca(ref name,ref tp,ref sz,_) => {
            let mut nprog = prog.clone();
            let mut updates = Vec::new();
            while let Some((cond,(cf_view,fr_view))) = ctxs.next(em)? {
                let (cf,cf_inp) = cf_view.get_with_inp(prog,prog_inp.clone());
                let dyn = match sz {
                    &None => None,
                    &Some(ref sz) => Some(translate_value(dl,&sz.val,&sz.tp,tps,cf,cf_inp,exprs,em)?)
                };
                let stat_bits = dl.type_size_in_bits(tp,tps);
                let stat_bytes = (stat_bits/8) as usize;
                let (sl,sl_inp) = match dyn {
                    None => MemSlice::alloca(stat_bytes,em),
                    Some(_) => panic!("Dynamic sized allocations not supported")
                };
                let alloc_view = fr_view.clone()
                    .then(AllocationsView::new())
                    .then(AssocView::new(instr_id.clone()));
                let (allocs,allocs_inp) = match alloc_view
                    .get_opt_with_inp(prog,prog_inp.clone()) {
                        None => (OptRef::Owned(Vec::new()),
                                 Transformation::id(0)),
                        Some((res,res_inp)) => (OptRef::Ref(res),res_inp)
                    };
                let (alloc_idx,nallocs,nallocs_inp)
                    = vec_pool_alloc(allocs,OptRef::Owned(sl),
                                     allocs_inp,sl_inp,
                                     &|_,_| false)?;
                alloc_view.insert(&mut nprog,nallocs.as_obj(),nallocs_inp,&mut updates);
                let instr_view = cf_view.clone()
                    .then(ValuesView::new())
                    .then(AssocView::new(name));
                let old_ptr = if cond.len()==0 {
                    None
                } else {
                    instr_view.get_opt_with_inp(prog,prog_inp.clone())
                };
                let (ptr1,ptr1_inp) = match old_ptr {
                    None => {
                        let (ch,ch_inp) = choice_empty();
                        (OptRef::Owned(ch),ch_inp)
                    },
                    Some((ptr,ptr_inp)) => match V::to_pointer(OptRef::Ref(ptr),ptr_inp) {
                        None => panic!("Value not a pointer"),
                        Some(r) => r
                    }
                };
                let rcond = if cond.len()==0 {
                    let c = em.const_bool(true)?;
                    Transformation::constant(vec![c])
                } else {
                    Transformation::and(cond.to_vec())
                };
                let (trg,trg_inp) = {
                    let Then(thr_view,fr_view_) = fr_view;
                    let (thr_id,thr_id_inp) = thread_view_to_idx(&thr_view,INDEX_WIDTH,em)?;
                    let (fr_id,fr_id_inp) = frame_view_to_idx(&fr_view_,INDEX_WIDTH,em)?;
                    let trg = PointerTrg::Stack(thr_id,INDEX_WIDTH,
                                                fr_id,INDEX_WIDTH,
                                                instr_id.clone(),INDEX_WIDTH);
                    let e = em.const_bitvec(INDEX_WIDTH,BigInt::from(alloc_idx))?;
                    let alloc_idx_inp = Transformation::constant(vec![e]);
                    let trg_inp = Transformation::concat(&[thr_id_inp,
                                                           fr_id_inp,
                                                           alloc_idx_inp]);
                    (trg,trg_inp)
                };
                let (ptr2,ptr2_inp) = choice_set_chosen(ptr1,
                                                        ptr1_inp,
                                                        rcond.clone(),
                                                        OptRef::Owned((trg,(Data((stat_bytes,0)),None))),
                                                        trg_inp)?;
                let (ptr3,ptr3_inp) = V::from_pointer(dl.pointer_alignment(0).0 as usize,ptr2,ptr2_inp);
                instr_view.insert(&mut nprog,ptr3.as_obj(),ptr3_inp,&mut updates);
                let act_view = cf_view.then(ActivationView::new());
                let (acts,acts_inp) = if cond.len()==0 {
                    let (r,inp) = choice_empty();
                    (OptRef::Owned(r),inp)
                } else {
                    let (r,inp) = act_view.get_with_inp(prog,prog_inp.clone());
                    (OptRef::Ref(r),inp)
                };
                let (nacts,nacts_inp) = choice_set_chosen(acts,acts_inp,rcond,
                                                          OptRef::Owned(Data(instr_id.next())),
                                                          Transformation::id(0))?;
                act_view.write(nacts.as_obj(),nacts_inp,&mut nprog,&mut updates);
            }
            let nprog_inp = finish_updates(updates,prog_inp);
            Ok((nprog,nprog_inp))
        },
        _ => unimplemented!()
    }
}

pub fn translate_value<'b,V,Em>(dl: &'b DataLayout,
                                value: &'b llvm_ir::Value,
                                tp: &'b Type,
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
        _ => unimplemented!()
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
            let (ptr,inp_ptr) = base_pointer_global(glb,em)?;
            let (bw,_,_) = dl.pointer_alignment(0);
            let (res,inp_res) = V::from_pointer((bw/8) as usize,
                                                OptRef::Owned(ptr),
                                                inp_ptr);
            Ok((res.as_obj(),inp_res))
        },
        &llvm_ir::Constant::Int(ref val) => match tp {
            &Type::Int(bw) => {
                let (rv,rv_inp) = V::const_int(bw,val.clone(),em)?;
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
                                coff += dl.type_size_in_bits(sub_tp,mp);
                            }
                            res.push((None,coff as usize));
                            &sub_tps[ridx]
                        },
                        _ => panic!("Struct not indexed by constant int")
                    },
                    &Type::Pointer(ref ptr_tp,_) => {
                        let sz = dl.type_size_in_bits(ptr_tp,mp);
                        let (idx,idx_inp) = translate_constant(dl,&el.val,ptr_tp,mp,em)?;
                        res.push((Some(V::to_offset(OptRef::Owned(idx),idx_inp)),sz as usize));
                        ptr_tp
                    },
                    &Type::Array(_,ref sub_tp) => {
                        let sz = dl.type_size_in_bits(sub_tp,mp);
                        let (idx,idx_inp) = translate_constant(dl,&el.val,sub_tp,mp,em)?;
                        res.push((Some(V::to_offset(OptRef::Owned(idx),idx_inp)),sz as usize));
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
        _ => unimplemented!()
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
    fn const_int<Em : Embed>(u64,BigInt,&mut Em) -> Result<(Self,Vec<Em::Expr>),Em::Error>;
    fn add<'a,'b,Em>(lhs: OptRef<'a,Self>,
                     rhs: OptRef<'a,Self>,
                     inp_l: Transf<Em>,
                     inp_r: Transf<Em>,
                     em: &mut Em)
                     -> Result<(OptRef<'a,Self>,Transf<Em>),()>
        where Em : Embed;
    fn to_offset<'a,Em : Embed>(OptRef<'a,Self>,Transf<Em>) -> (Singleton,Transf<Em>);
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
    Pointer(Ptr),
    Vector(Vec<CompValue<Ptr,V>>)
}

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub struct ByteWidth<V> {
    value: V,
    byte_width: usize
}

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub enum BitVecValue {
    BoolValue(usize),
    BitVecValue(usize)
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
                        let outp = comb(inp_x,inp_y,em)?;
                        Ok(Some((OptRef::Owned(BitVecValue::BitVecValue(sz1)),outp)))
                    } else {
                        Ok(None)
                    }
            },
            BitVecValue::BitVecValue(sz1) => match *y.as_ref() {
                BitVecValue::BoolValue(sz2) => if sz1==sz2 {
                    let outp = comb(inp_x,inp_y,em)?;
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
        let tp = match v.as_ref() {
            &BitVecValue::BoolValue(_) => Sort::from_kind(SortKind::Bool),
            &BitVecValue::BitVecValue(w) => Sort::from_kind(SortKind::BitVec(w))
        };
        (Singleton(tp),tr)
    }
    fn const_int<Em : Embed>(bw: u64,val: BigInt,em: &mut Em) -> Result<(BitVecValue,Vec<Em::Expr>),Em::Error> {
        if val==BigInt::from(0) || val==BigInt::from(1) {
            let el = em.const_bool(val==BigInt::from(1))?;
            Ok((BitVecValue::BoolValue(bw as usize),
                vec![el]))
        } else {
            let el = em.const_bitvec(bw as usize,val)?;
            Ok((BitVecValue::BitVecValue(bw as usize),
                vec![el]))
        }
    }
    fn add<'a,'b,Em>(lhs: OptRef<'a,BitVecValue>,
                     rhs: OptRef<'a,BitVecValue>,
                     inp_l: Transf<Em>,
                     inp_r: Transf<Em>,
                     _: &mut Em)
                     -> Result<(OptRef<'a,BitVecValue>,Transf<Em>),()>
        where Em : Embed {

        match *lhs.as_ref() {
            BitVecValue::BoolValue(sz1) => match *rhs.as_ref() {
                BitVecValue::BoolValue(sz2) => {
                    assert_eq!(sz1,sz2);
                    let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                        let bv0 = em.const_bitvec(sz1,BigInt::from(0))?;
                        let bv1 = em.const_bitvec(sz1,BigInt::from(1))?;
                        let rlhs = em.ite(lhs[0].clone(),bv1.clone(),bv0.clone())?;
                        let rrhs = em.ite(rhs[1].clone(),bv1,bv0)?;
                        arr.push(em.bvadd(rlhs,rrhs)?);
                        Ok(())
                    };
                    Ok((OptRef::Owned(BitVecValue::BitVecValue(sz1)),
                        Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                },
                BitVecValue::BitVecValue(sz2) => {
                    assert_eq!(sz1,sz2);
                    let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                        let bv0 = em.const_bitvec(sz1,BigInt::from(0))?;
                        let bv1 = em.const_bitvec(sz1,BigInt::from(1))?;
                        let rlhs = em.ite(lhs[0].clone(),bv1,bv0)?;
                        arr.push(em.bvadd(rlhs,rhs[0].clone())?);
                        Ok(())
                    };
                    Ok((OptRef::Owned(BitVecValue::BitVecValue(sz1)),
                        Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                }
            },
            BitVecValue::BitVecValue(sz1) => match *rhs.as_ref() {
                BitVecValue::BoolValue(sz2) => {
                    assert_eq!(sz1,sz2);
                    let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                        let bv0 = em.const_bitvec(sz1,BigInt::from(0))?;
                        let bv1 = em.const_bitvec(sz1,BigInt::from(1))?;
                        let rrhs = em.ite(rhs[1].clone(),bv1,bv0)?;
                        arr.push(em.bvadd(lhs[0].clone(),rrhs)?);
                        Ok(())
                    };
                    Ok((OptRef::Owned(BitVecValue::BitVecValue(sz1)),
                        Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                },
                BitVecValue::BitVecValue(sz2) => {
                    assert_eq!(sz1,sz2);
                    let f = move |lhs : &[Em::Expr],rhs : &[Em::Expr],arr : &mut Vec<Em::Expr>,em : &mut Em| {
                        arr.push(em.bvadd(lhs[0].clone(),rhs[0].clone())?);
                        Ok(())
                    };
                    Ok((OptRef::Owned(BitVecValue::BitVecValue(sz1)),
                        Transformation::zip2(1,Box::new(f),inp_l,inp_r)))
                }
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

impl<Ptr,V> CompValue<Ptr,V> {
    pub fn lower<'a>(x: OptRef<'a,Self>) -> CompValue<OptRef<'a,Ptr>,OptRef<'a,V>> {
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
}

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
                match Ptr::combine(rvx,rvy,inp_x,inp_y,
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
                match Ptr::combine(rvx,rvy,inp_x,inp_y,
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

impl<Ptr : Composite+Clone,V : IntValue+Clone> IntValue for CompValue<Ptr,V> {
    fn to_offset<'a,Em : Embed>(v: OptRef<'a,Self>,tr: Transf<Em>) -> (Singleton,Transf<Em>) {
        match v {
            OptRef::Owned(CompValue::Value(pv))
                => V::to_offset(OptRef::Owned(pv),tr),
            OptRef::Ref(&CompValue::Value(ref pv))
                => V::to_offset(OptRef::Ref(pv),tr),
            _ => panic!("Pointer cannot be used as offset")
        }
    }
    fn const_int<Em : Embed>(bw: u64,val: BigInt,em: &mut Em) -> Result<(Self,Vec<Em::Expr>),Em::Error> {
        let (v,inp_v) = V::const_int(bw,val,em)?;
        Ok((CompValue::Value(v),inp_v))
    }
    fn add<'a,'b,Em>(lhs: OptRef<'a,Self>,
                     rhs: OptRef<'a,Self>,
                     inp_l: Transf<Em>,
                     inp_r: Transf<Em>,
                     em: &mut Em)
                     -> Result<(OptRef<'a,Self>,Transf<Em>),()>
        where Em : Embed {
        let rlhs = match lhs {
            OptRef::Owned(CompValue::Value(v))
                => OptRef::Owned(v),
            OptRef::Ref(&CompValue::Value(ref v))
                => OptRef::Ref(v),
            _ => panic!("Cannot add pointers")
        };
        let rrhs = match rhs {
            OptRef::Owned(CompValue::Value(v))
                => OptRef::Owned(v),
            OptRef::Ref(&CompValue::Value(ref v))
                => OptRef::Ref(v),
            _ => panic!("Cannot add pointers")
        };
        let (res,inp_res) = V::add(rlhs,rrhs,inp_l,inp_r,em)?;
        Ok((OptRef::Owned(CompValue::Value(res.as_obj())),
            inp_res))
    }

}

impl<Ptr : Bytes+Clone,V : Bytes+Clone> Bytes for CompValue<Ptr,V> {
    fn byte_width(&self) -> usize {
        match self {
            &CompValue::Value(ref v) => v.byte_width(),
            &CompValue::Pointer(ref p) => p.byte_width(),
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
            OptRef::Ref(&CompValue::Pointer(ref vx)) => match Ptr::extract_bytes(OptRef::Ref(vx),inp_x,start,len,em)? {
                None => Ok(None),
                Some((nvx,inp_nvx)) => Ok(Some((OptRef::Owned(CompValue::Pointer(nvx.as_obj())),
                                                inp_nvx)))
            },
            OptRef::Owned(CompValue::Pointer(vx)) => match Ptr::extract_bytes(OptRef::Owned(vx),inp_x,start,len,em)? {
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
        let (ptr,inp_ptr) = Ptr::from_pointer(bw,base,inp_base);
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
        Ptr::to_pointer(rptr,inp_ptr)
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
