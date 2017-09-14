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
use self::smtrs::domain::{Domain};
use self::smtrs::types::{Sort,SortKind,Value};
use self::num_bigint::BigInt;
use self::num_traits::cast::ToPrimitive;
use std::fmt::Debug;
use std::collections::HashMap;
use self::mem::{Bytes,MemSlice};
use self::frame::*;
use self::thread::*;
use self::program::*;
use self::error::{Errors,Error,add_error};
use self::pointer::*;
use self::llvm_ir::Module;
use self::llvm_ir::datalayout::{DataLayout};
use self::llvm_ir::types::{Type};

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash,Clone,Debug)]
pub struct InstructionRef<'a> {
    basic_block: &'a String,
    instruction: usize
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
    where V : Bytes+Clone, Em : Embed {

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
    let (act_main,inp_act_main) = choice_insert(act_main0,inp_act_main0,
                                                Transformation::const_bool(true,em)?,
                                                OptRef::Owned(Data(InstructionRef { basic_block: main_blk,
                                                                                    instruction: 0 })),
                                                Transformation::id(0))?;
    let (phi_main,inp_phi_main) = choice_empty();

    let (cf_main,inp_cf_main) = call_frame(values_main,inp_values_main,
                                           OptRef::Owned(args),inp_args,
                                           act_main,inp_act_main,
                                           phi_main,inp_phi_main);
    let (prev_main0,inp_prev_main0) = choice_empty();
    let (prev_main,inp_prev_main) = choice_insert(prev_main0,inp_prev_main0,
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
    let (top_main,inp_top_main) = choice_insert(top_main0,inp_top_main0,
                                                Transformation::const_bool(true,em)?,
                                                OptRef::Owned(Data(None)),
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

    let (globals,inp_globals) = assoc_empty()?;
    // FIXME: Translate globals

    let (heap,inp_heap) = assoc_empty()?;
    
    Ok(program(threads,inp_threads,globals,inp_globals,heap,inp_heap))
}
                                  

pub fn translate_instr<'a,'b : 'a,V,Em
                       >(dl: &'b DataLayout,
                         tps: &'b HashMap<String,Type>,
                         thread_id: &ThreadId<'b>,
                         cf_id: &CallId<'b>,
                         instr_id: &InstructionRef<'b>,
                         instr: &'b llvm_ir::Instruction,
                         next_instr_id: &InstructionRef<'b>,
                         prog: OptRef<'a,Program<'b,V>>,
                         inp: OptRef<'a,ProgramInput<'b,V>>,
                         prog_inp: Transf<Em>,
                         inp_inp: Transf<Em>,
                         exprs: &[Em::Expr],
                         em: &mut Em)
                         -> Result<(OptRef<'a,Program<'b,V>>,
                                    Transf<Em>),
                                   TrErr<'b,V,Em::Error>>
    where V : Bytes+Clone+Pointer<'b>,Em : DeriveValues {
    let (step,thr_idx) = match program_input_thread_activation(inp.to_ref(),inp_inp,thread_id,em)? {
        Some(r) => r,
        None => {
            let mut rinp = inp.as_obj();
            rinp.add_thread(thread_id.clone());
            return Err(TrErr::InputNeeded(rinp))
        }
    };
    let (threads,inp_threads,globals,inp_globals,heap,inp_heap)
        = decompose_program(prog,prog_inp);
    let (nthrs,inp_nthrs) = {
        let (thrs,inp_thrs) = assoc_get(threads.to_ref(),inp_threads.clone(),thread_id)?.expect("Thread not found");
        let (nthr,inp_nthr) = {
            let (thr,thr_inp) = get_vec_elem_dyn(thrs.to_ref(),thr_idx.clone(),inp_thrs.clone(),exprs,em)?.expect("Thread not found");
        
            let (cs,inp_cs,st,inp_st,top,inp_top,ret,inp_ret) = decompose_thread(thr,thr_inp);
            let cf_act = call_frame_activation(top.to_ref(),inp_top.clone(),cf_id,em)?;
            match instr.content {
                llvm_ir::InstructionC::Alloca(ref name,ref tp,None,_) => {
                    let sz = dl.type_size_in_bits(tp,tps) / 8;
                    let mut cur_cs = cs;
                    let mut cur_inp_cs = inp_cs;
                    let mut cur_st = st;
                    let mut cur_inp_st = inp_st;
                    let (ptr_init,inp_ptr_init) = choice_empty();
                    let mut ptr : OptRef<'a,BasePointer<'b>> = ptr_init;
                    let mut inp_ptr : Transf<Em> = inp_ptr_init;
                    // Iterate over all possible call frames
                    for (el,cond,inp) in top.as_ref().choices(inp_top.clone()) {
                        let vcond = &cond.get(exprs,0,em)?;
                        let always = match em.derive_const(vcond)? {
                        Some(Value::Bool(false)) => continue,
                            Some(Value::Bool(true)) => true,
                            _ => false
                        };
                        let rcond = Transformation::and(vec![step.clone(),cf_act.clone(),cond.clone()]);
                        match el.0 {
                            None => {},
                            Some(FrameId::Call(ref id)) => if *id==*cf_id {
                                let (ncs,inp_ncs) = {
                                    let (ncfs,inp_ncfs) = {
                                        let (cfs,inp_cfs) = assoc_get(cur_cs.to_ref(),cur_inp_cs.clone(),cf_id)?.expect("Internal error");
                                        let (ntup,inp_ntup) = {
                                            let (tup,inp_tup) = bv_vec_stack_get_top(cfs.to_ref(),inp_cfs.clone(),exprs,em)?.expect("Internal error");
                                            let (cf,inp_cf,fr,inp_fr) = decompose_tuple(tup,inp_tup);
                                            let (prev,inp_prev,alloc,inp_alloc) = decompose_frame(fr,inp_fr);
                                            let (sl,inp_sl) = MemSlice::alloca(sz as usize,em);
                                            let (pos,nsls,inp_nsls) = match assoc_get(alloc.to_ref(),inp_alloc.clone(),instr_id)? {
                                                None => (0,OptRef::Owned(vec![sl]),inp_sl),
                                                Some((sls,inp_sls)) => vec_pool_alloc(OptRef::Owned(sls.as_obj()),OptRef::Owned(sl),inp_sls,inp_sl,&|el,_| el.is_free())?
                                            };
                                            let trg = OptRef::Owned((PointerTrg::Heap(instr_id.clone(),INDEX_WIDTH),
                                                                     offset_zero(INDEX_WIDTH)));
                                            let inp_trg = {
                                                let c = em.const_bitvec(INDEX_WIDTH,BigInt::from(pos))?;
                                                Transformation::constant(vec![c])
                                            };
                                            let (nptr,inp_nptr) = choice_insert(ptr,inp_ptr,cond,trg,inp_trg)?;
                                            ptr = nptr;
                                            inp_ptr = inp_nptr;
                                            let (nalloc,inp_nalloc) = assoc_insert(alloc,inp_alloc,instr_id,nsls,inp_nsls)?;
                                            let (nfr,inp_nfr) = frame(prev,inp_prev,nalloc,inp_nalloc);
                                            tuple(cf,nfr,inp_cf,inp_nfr)
                                        };
                                        bv_vec_stack_set_top(cfs,inp_cfs,ntup,inp_ntup,exprs,em)?.expect("Internal error")
                                    };
                                    assoc_insert(cur_cs,cur_inp_cs,cf_id,ncfs,inp_ncfs)?
                                };
                                cur_cs = ncs;
                                cur_inp_cs = inp_ncs;
                            },
                            Some(FrameId::Stack(ref id,ref save_call)) => if *id==*cf_id {
                                unimplemented!()
                            }
                        }
                    }
                    let (bw,_,_) = dl.pointer_alignment(0);
                    let (pval,inp_pval) = V::from_pointer((bw/8) as usize,ptr,inp_ptr);
                    let (ncfs,inp_ncfs) = {
                        let (cfs,inp_cfs) = assoc_get(cur_cs.to_ref(),cur_inp_cs.clone(),cf_id)?.expect("Internal error");
                        let cfs_top_bw = cfs.as_ref().top;
                        let mut accessor_cf = bv_vec_stack_access_top(cfs,inp_cfs,exprs,em)?;
                        while let Some((cond,cf_tup,inp_cf_tup)) = accessor_cf.next()? {
                            let cvec = match cond {
                                None => vec![step.clone(),cf_act.clone()],
                                Some(ccond) => vec![step.clone(),cf_act.clone(),ccond]
                            };
                            let rcond = Transformation::and(cvec);
                            let (ncf_tup,inp_ncf_tup) = {
                                let (cf,inp_cf,fr,inp_fr) = decompose_tuple(OptRef::Ref(cf_tup),inp_cf_tup.clone());
                                let (vals,inp_vals,args,inp_args,acts,inp_acts,phi,inp_phi) = decompose_callframe(cf,inp_cf);
                                let (nptr,inp_nptr) = match assoc_get(vals.to_ref(),inp_vals.clone(),&name)? {
                                    None => (pval.to_ref(),inp_pval.clone()),
                                    Some((oval,inp_oval)) => {
                                        
                                        let (nval,inp_nval) = ite(pval.to_ref(),oval,rcond.clone(),inp_pval.clone(),inp_oval,em)?.expect("Cannot merge pointers");
                                        (nval.to_owned(),inp_nval)
                                    }
                                };
                                let (nacts,inp_nacts) = choice_set_chosen(acts,inp_acts,rcond,
                                                                          OptRef::Owned(Data(next_instr_id.clone())),
                                                                          Transformation::id(0))?;
                                let (nvals,inp_nvals) = assoc_insert(vals,inp_vals,&name,nptr,inp_nptr)?;
                                let (ncf,inp_ncf) = call_frame(nvals,inp_nvals,args,inp_args,nacts,inp_nacts,phi,inp_phi);
                                let (ncf_tup,inp_ncf_tup) = tuple(ncf,fr,inp_ncf,inp_fr);
                                (ncf_tup.as_obj(),inp_ncf_tup)
                            };
                            *cf_tup = ncf_tup;
                            *inp_cf_tup = inp_ncf_tup;
                        }
                        let (ncfs_,inp_ncfs) = accessor_cf.finish();
                        let ncfs = OptRef::Owned(BitVecVectorStack { top: cfs_top_bw,
                                                                     elements: ncfs_ });
                        (ncfs,inp_ncfs)
                    };
                    let (ncs,inp_ncs) = assoc_insert(cur_cs,cur_inp_cs,cf_id,ncfs,inp_ncfs)?;
                    thread(ncs,inp_ncs,
                           cur_st,cur_inp_st,
                           top,inp_top,
                           ret,inp_ret)
                    
                },
                _ => unimplemented!()
            }
        };
        set_vec_elem_dyn(thrs,nthr,thr_idx,inp_thrs,inp_nthr,exprs,em)?.expect("Cannot merge thread")
    };
    let (nthreads,inp_nthreads) = assoc_insert(threads,inp_threads,thread_id,nthrs,inp_nthrs)?;
    let (nprog,inp_nprog) = program(nthreads,inp_nthreads,globals,inp_globals,heap,inp_heap);
    Ok((nprog,inp_nprog))
}

pub fn translate_value<'a,'b,V,Em>(dl: &'b DataLayout,
                                   value: &'b llvm_ir::Value,
                                   tp: &'b Type,
                                   tps: &'b HashMap<String,Type>,
                                   cf: OptRef<'a,CallFrame<'b,V>>,
                                   cf_inp: Transf<Em>,
                                   exprs: &[Em::Expr],
                                   em: &mut Em)
                                   -> Result<(OptRef<'a,V>,Transf<Em>),Em::Error>
    where V : Bytes+Pointer<'b>+IntValue+Vector+Clone,Em : DeriveValues {
    match value {
        &llvm_ir::Value::Constant(ref c) => {
            let (obj,els) = translate_constant(dl,c,tp,tps,em)?;
            Ok((obj,els))
        },
        &llvm_ir::Value::Local(ref name) => {
            let (vals,vals_inp) = call_frame_get_values(cf,cf_inp);
            match assoc_get(vals,vals_inp,&name)? {
                None => panic!("Local name {} not found",name),
                Some(r) => Ok(r)
            }
        },
        _ => unimplemented!()
    }
}

pub fn translate_constant<'a,'b : 'a,V,Em>(dl: &'b DataLayout,
                                           c: &'b llvm_ir::Constant,
                                           tp: &'b Type,
                                           mp: &HashMap<String,Type>,
                                           em: &mut Em)
                                           -> Result<(OptRef<'a,V>,Transf<Em>),Em::Error>
    where V : Bytes+Pointer<'b>+IntValue+Vector+Clone, Em : Embed {

    match c {
        &llvm_ir::Constant::Global(ref glb) => {
            let (sz,_,_) = dl.pointer_alignment(0);
            let (ptr,inp_ptr) = base_pointer_global(glb,em)?;
            let (bw,_,_) = dl.pointer_alignment(0);
            let res : (OptRef<'a,V>,Transf<Em>) = V::from_pointer((bw/8) as usize,ptr,inp_ptr);
            Ok(res)
        },
        &llvm_ir::Constant::Int(ref val) => match tp {
            &Type::Int(bw) => {
                let (rv,rv_inp) = V::const_int(bw,val.clone(),em)?;
                Ok((OptRef::Owned(rv),Transformation::constant(rv_inp)))
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
                let (val,c) = translate_constant(dl,el,el_tp,mp,em)?;
                varr.push(val.as_obj());
                earr.push(c);
            }
            let (res,inp_res) = V::vector(OptRef::Owned(varr),earr,em)?;
            Ok((res,inp_res))
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
                        res.push((Some(V::to_offset(idx,idx_inp)),sz as usize));
                        ptr_tp
                    },
                    &Type::Array(_,ref sub_tp) => {
                        let sz = dl.type_size_in_bits(sub_tp,mp);
                        let (idx,idx_inp) = translate_constant(dl,&el.val,sub_tp,mp,em)?;
                        res.push((Some(V::to_offset(idx,idx_inp)),sz as usize));
                        sub_tp
                    },
                    _ => unimplemented!()
                }
            }
            let (base,base_inp) : (OptRef<'a,V>,Transf<Em>) = translate_constant(dl,&gep.ptr.val,&gep.ptr.tp,mp,em)?;
            let bw = base.as_ref().byte_width();
            let (ptr,ptr_inp) = V::to_pointer(base,base_inp).expect("Cannot convert to pointer");
            let (nptr,nptr_inp) = base_pointer_gep(ptr,ptr_inp,res,em)?;
            Ok(V::from_pointer(bw,nptr,nptr_inp))
        },
        _ => unimplemented!()
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
    Pointer(Ptr)
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
            &BitVecValue::BitVecValue(sz) => {
                let rsz = sz/8;
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
            OptRef::Ref(&CompValue::Value(ref v))
                => CompValue::Value(OptRef::Ref(v)),
            OptRef::Ref(&CompValue::Pointer(ref p))
                => CompValue::Pointer(OptRef::Ref(p))
        }
    }
}

impl<Ptr : Composite+Clone,V : Composite+Clone> Composite for CompValue<Ptr,V> {
    fn num_elem(&self) -> usize {
        match self {
            &CompValue::Value(ref v) => v.num_elem(),
            &CompValue::Pointer(ref p) => p.num_elem()
        }
    }
    fn elem_sort<Em : Embed>(&self,n:usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        match self {
            &CompValue::Value(ref v) => v.elem_sort(n,em),
            &CompValue::Pointer(ref p) => p.elem_sort(n,em)
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

        let rx = CompValue::lower(x);
        let ry = CompValue::lower(y);

        match rx {
            CompValue::Value(vx) => match ry {
                CompValue::Value(vy)
                    => match V::combine(vx,vy,inp_x,inp_y,
                                        comb,only_l,only_r,em)? {
                        None => Ok(None),
                        Some((nv,inp_nv)) => Ok(Some((OptRef::Owned(CompValue::Value(nv.as_obj())),inp_nv)))
                    },
                CompValue::Pointer(_) => Ok(None)
            },
            CompValue::Pointer(px) => match ry {
                CompValue::Pointer(py)
                    => match Ptr::combine(px,py,inp_x,inp_y,
                                          comb,only_l,only_r,em)? {
                        None => Ok(None),
                        Some((np,inp_np)) => Ok(Some((OptRef::Owned(CompValue::Pointer(np.as_obj())),inp_np)))
                    },
                CompValue::Value(_) => Ok(None)
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
            &CompValue::Pointer(ref p) => p.byte_width()
        }
    }
    fn extract_bytes<'a,Em : Embed>(x: OptRef<'a,Self>,
                                    inp_x: Transf<Em>,
                                    start: usize,
                                    len: usize,
                                    em: &mut Em)
                                    -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error> {
        let rx = CompValue::lower(x);
        match rx {
            CompValue::Value(vx) => match V::extract_bytes(vx,inp_x,start,len,em)? {
                None => Ok(None),
                Some((nvx,inp_nvx)) => Ok(Some((OptRef::Owned(CompValue::Value(nvx.as_obj())),
                                                inp_nvx))),
            },
            CompValue::Pointer(px) => match Ptr::extract_bytes(px,inp_x,start,len,em)? {
                None => Ok(None),
                Some((npx,inp_npx)) => Ok(Some((OptRef::Owned(CompValue::Pointer(npx.as_obj())),
                                                inp_npx)))
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
