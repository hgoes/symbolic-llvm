
use super::program::*;
use super::frame::*;
use super::mem::*;
use super::pointer::*;
use super::{InstructionRef,INDEX_WIDTH,IntValue};
use smtrs::composite::*;
use smtrs::embed::{DeriveValues};
use smtrs::types::{Value};
use num_bigint::BigUint;
use num_traits::ToPrimitive;
use llvm_ir::datalayout::DataLayout;
use std::fmt::Debug;

pub trait Library<'a,V : 'a+Bytes+FromConst<'a>> {
    fn call<RetV,Em : DeriveValues>(&self,
                                    &'a String,
                                    &Vec<V>,Transf<Em>,
                                    Option<RetV>,
                                    &'a DataLayout,
                                    InstructionRef<'a>,
                                    &mut Vec<Transf<Em>>,
                                    &Program<'a,V>,Transf<Em>,
                                    &mut Program<'a,V>,&mut Updates<Em>,
                                    &[Em::Expr],&mut Em)
                                    -> Result<bool,Em::Error>
        where RetV : ViewInsert<Viewed=Program<'a,V>,Element=V>+ViewMut;
}

pub struct StdLib {}

impl<'a,V : 'a+Bytes+FromConst<'a>+IntValue+Pointer<'a>+Debug> Library<'a,V> for StdLib {
    fn call<RetV,Em : DeriveValues>(&self,
                                    name: &'a String,
                                    args: &Vec<V>,
                                    args_inp: Transf<Em>,
                                    ret_view: Option<RetV>,
                                    dl: &'a DataLayout,
                                    instr_id: InstructionRef<'a>,
                                    conds: &mut Vec<Transf<Em>>,
                                    prog: &Program<'a,V>,
                                    prog_inp: Transf<Em>,
                                    nprog: &mut Program<'a,V>,
                                    updates: &mut Updates<Em>,
                                    exprs: &[Em::Expr],
                                    em: &mut Em)
                                    -> Result<bool,Em::Error>
        where RetV : ViewInsert<Viewed=Program<'a,V>,Element=V>+ViewMut {
        match name.as_ref() {
            "malloc" => {
                let (sz,sz_inp) = get_vec_elem(0,OptRef::Ref(args),args_inp)?;
                let (rsz,rsz_inp) = V::to_offset(sz,sz_inp);
                let csz = rsz_inp.get(exprs,0,em)?;
                let stat_sz = match em.derive_const(&csz)? {
                    Some(Value::BitVec(_,rv)) => rv.to_usize().unwrap(),
                    Some(c) => panic!("Construct malloc size from: {:?}",c),
                    None => panic!("Dynamic malloc not supported")
                };
                // Create slice
                let (sl,sl_inp) = MemSlice::alloca(stat_sz,em);
                // Insert slice into heap
                let heap_pool_view = HeapView::new().then(AssocView::new(instr_id));
                let (heap_pool,heap_pool_inp)
                    = match heap_pool_view.get_opt_with_inp(prog,
                                                            prog_inp.clone()) {
                        None => (OptRef::Owned(Vec::new()),Transformation::id(0)),
                        Some((p,inp)) => (OptRef::Ref(p),inp)
                    };
                let (heap_idx,nheap_pool,nheap_pool_inp)
                    = vec_pool_alloc(heap_pool,OptRef::Owned(sl),
                                     heap_pool_inp,sl_inp,
                                     &|_,_| false)?;
                heap_pool_view.insert(nprog,
                                      nheap_pool.as_obj(),nheap_pool_inp,
                                      updates);
                // Generate the new pointer
                let trg = PointerTrg::Heap(instr_id,INDEX_WIDTH);
                let trg_inp = {
                    let e = em.const_bitvec(INDEX_WIDTH,BigUint::from(heap_idx))?;
                    Transformation::constant(vec![e])
                                        };
                let rcond = if conds.len()==0 {
                    let c = em.const_bool(true)?;
                    Transformation::constant(vec![c])
                } else {
                    Transformation::and(conds.to_vec())
                };
                let (ptr_,ptr_inp_) = choice_empty();
                                        let (ptr,ptr_inp) = choice_insert(OptRef::Owned(ptr_),ptr_inp_,rcond.clone(),
                                                                          OptRef::Owned((trg,(Data((stat_sz,0)),None))),trg_inp)?;
                // Insert the pointer
                let rret = match ret_view {
                    None => panic!("malloc without return"),
                    Some(r) => r
                };
                let (val,val_inp) = V::from_pointer((dl.pointer_alignment(0).0/8) as usize,
                                                    ptr,ptr_inp);
                rret.insert_cond(nprog,val.as_obj(),val_inp,conds,updates,prog_inp,em)?;
                Ok(true)
            },
            "realloc" => {
                let (ptr,ptr_inp) = get_vec_elem(0,OptRef::Ref(args),
                                                 args_inp.clone())?;
                // Insert the pointer
                let rret = match ret_view {
                    None => panic!("realloc without return"),
                    Some(r) => r
                };
                rret.insert_cond(nprog,ptr.as_ref().clone(),ptr_inp.clone(),
                                 conds,updates,prog_inp,em)?;
                
                let (sz,sz_inp) = get_vec_elem(1,OptRef::Ref(args),args_inp)?;
                let (rptr,rptr_inp) = match V::to_pointer(ptr,ptr_inp) {
                    None => panic!("realloc argument not a pointer"),
                    Some(r) => r
                };
                let (rsz,rsz_inp) = V::to_offset(sz,sz_inp);
                let csz = rsz_inp.get(exprs,0,em)?;
                let stat_sz = match em.derive_const(&csz)? {
                    Some(Value::BitVec(_,rv)) => rv.to_usize().unwrap(),
                    Some(c) => panic!("Construct realloc size from: {:?}",c),
                    None => panic!("Dynamic realloc not supported")
                };
                let mut ptr_iter = rptr.as_ref().chosen(rptr_inp.clone());
                let cpos = conds.len();
                while let Some(base_view) = ptr_iter.next(conds,cpos,em)? {
                    let (trg_off,trg_off_inp)
                        = base_view.get_with_inp(rptr.as_ref(),
                                                 rptr_inp.clone());
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
                    while let Some(lookup) = lookup_iter.next(conds,cpos,em)? {
                        let pview = match lookup {
                            MemLookup::Slice(pview) => pview,
                            _ => panic!("realloc target not an allocation")
                        };
                        let sl = pview.get_el_mut(nprog);
                        sl.realloc(stat_sz);
                    }
                }
                conds.truncate(cpos);
                Ok(true)
            },
            x if x.starts_with("llvm.expect.") => {
                let (val,val_inp) = get_vec_elem(0,OptRef::Ref(args),
                                                 args_inp.clone())?;
                let rret = match ret_view {
                    None => panic!("llvm.expect without return"),
                    Some(r) => r
                };
                rret.insert_cond(nprog,val.as_obj(),val_inp,
                                 conds,updates,prog_inp,em)?;
                Ok(true)
            },
            _ => Ok(false)
        }
    }
}
