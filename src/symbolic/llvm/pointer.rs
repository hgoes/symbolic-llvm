extern crate smtrs;

use self::smtrs::composite::*;
use self::smtrs::embed::Embed;
use self::smtrs::types::{Sort,SortKind};
use self::smtrs::expr::Expr;
use super::{InstructionRef};
use super::frame::{FrameId};
use super::program::{ThreadId};
use num_bigint::BigUint;
use super::mem::Bytes;
use super::IntValue;
use std::fmt;

pub trait Pointer<'b> : Composite {
    fn from_pointer<'a,Em : Embed>(usize,OptRef<'a,BasePointer<'b>>,Transf<Em>) -> (OptRef<'a,Self>,Transf<Em>);
    fn to_pointer<'a,Em : Embed>(OptRef<'a,Self>,Transf<Em>) -> Option<(OptRef<'a,BasePointer<'b>>,Transf<Em>)>;
    fn ptr_eq<Em : Embed>(&Self,Transf<Em>,&Self,Transf<Em>) -> Transf<Em>;
    fn ptr_lt<Em : Embed>(&Self,Transf<Em>,
                          &Self,Transf<Em>,&mut Em)
                          -> Result<Transf<Em>,Em::Error>;
}

pub type BasePointer<'a> = Choice<(PointerTrg<'a>,Offset)>;

pub type Offset = (Data<(usize,usize)>,Option<Singleton>);

pub fn base_pointer_null<'a,'b,Em>(em: &mut Em)
                                   -> Result<(BasePointer<'a>,
                                              Transf<Em>),Em::Error>
    where Em : Embed {
    let (ch0,inp_ch0) = choice_empty();
    let (ch,inp_ch) = choice_insert(OptRef::Owned(ch0),inp_ch0,Transformation::const_bool(true,em)?,
                                    OptRef::Owned((PointerTrg::Null,
                                                   (Data((0,0)),None))),
                                    Transformation::id(0))?;
    Ok((ch.as_obj(),inp_ch))
}

pub fn base_pointer_global<'a,'b,Em>(mult: usize,
                                     name: &'a String,
                                     em: &mut Em)
                                     -> Result<(BasePointer<'a>,
                                                Transf<Em>),Em::Error>
    where Em : Embed {
    let (ch0,inp_ch0) = choice_empty();
    let (ch,inp_ch) = choice_insert(OptRef::Owned(ch0),inp_ch0,Transformation::const_bool(true,em)?,
                                    OptRef::Owned((PointerTrg::Global(name),
                                                   (Data((mult,0)),None))),
                                    Transformation::id(0))?;
    Ok((ch.as_obj(),inp_ch))
}

pub fn base_pointer_gep<'a,'b,'c,Em : Embed>(ptr: OptRef<'a,BasePointer<'b>>,
                                             inp_ptr: Transf<Em>,
                                             gep: Vec<(Option<(Singleton,Transf<Em>)>,usize)>,
                                             em: &mut Em)
                                             -> Result<(OptRef<'c,BasePointer<'b>>,Transf<Em>),Em::Error> {
    let (nptr,inp_nptr) = ptr.as_obj().map(inp_ptr,em,&|inp_cond,base,inp_base,_| {
        let (trg,inp_trg,off,inp_off) = decompose_tuple(OptRef::Owned(base),inp_base);
        let mut coff = off;
        let mut inp_coff = inp_off;
        for &(ref dyn,stat) in gep.iter() {
            let (noff,inp_noff) = match dyn {
                &None => offset_advance(coff,inp_coff,stat),
                &Some((ref rdyn,ref inp_rdyn)) => match offset_advance_dyn(coff,inp_coff,rdyn.clone(),inp_rdyn.clone())? {
                    None => panic!("Cannot advance pointer dynamically here"),
                    Some(r) => r
                }
            };
            coff = noff;
            inp_coff = inp_noff;
        }
        let (nbase,inp_nbase) = tuple(trg,coff,inp_trg,inp_coff);
        Ok((inp_cond,nbase.as_obj(),inp_nbase))
    })?;
    Ok((OptRef::Owned(nptr),inp_nptr))
}

pub fn offset_zero(sz: usize) -> Offset {
    (Data((0,sz)),None)
}

pub fn offset_advance<'a,Em : Embed>(offset: OptRef<'a,Offset>,inp_offset: Transf<Em>,add: usize)
                                     -> (OptRef<'a,Offset>,Transf<Em>) {
    let mut noff = offset.as_obj();
    ((noff.0).0).1 += add;
    (OptRef::Owned(noff),inp_offset)
}

pub fn offset_advance_dyn<'a,Em : Embed>(offset: OptRef<'a,Offset>,inp_offset: Transf<Em>,
                                         add: Singleton,inp_add: Transf<Em>)
                                         -> Result<Option<(OptRef<'a,Offset>,Transf<Em>)>,Em::Error> {
    let has_offset = match offset.as_ref().1 {
        Some(ref tp) => if *tp==add {
            true
        } else {
            return Ok(None)
        },
        None => false
    };
    if has_offset {
        let add_fun = |lhs:&[Em::Expr],rhs:&[Em::Expr],res:&mut Vec<Em::Expr>,em:&mut Em| {
            let tp = em.type_of(&lhs[0])?;
            let r = match em.unbed_sort(&tp)? {
                SortKind::Int => em.add_int(vec![lhs[0].clone(),rhs[0].clone()])?,
                SortKind::BitVec(_) => em.bvadd(lhs[0].clone(),rhs[0].clone())?,
                _ => panic!("Invalid offset type: {:?}",tp)
            };
            res.push(r);
            Ok(())
        };
        let ninp = Transformation::zip2(1,Box::new(add_fun),inp_offset,inp_add);
        return Ok(Some((offset,ninp)))
    } else {
        let mut noff = offset.as_obj();
        noff.1 = Some(add);
        Ok(Some((OptRef::Owned(noff),inp_add)))
    }
}

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash,Clone,Debug)]
pub enum PointerTrg<'a> {
    Null,
    Global(&'a String),
    Heap(InstructionRef<'a>,usize),
    Stack(ThreadId<'a>,usize, // Thread selector
          FrameId<'a>,usize,                   // Frame selector
          InstructionRef<'a>,usize),           // Allocation selector
    Aux(usize),
    AuxArray
}

impl<'b> HasSorts for PointerTrg<'b> {
    fn num_elem(&self) -> usize {
        match *self {
            PointerTrg::Null => 0,
            PointerTrg::Global(_) => 0,
            PointerTrg::Heap(_,_) => 1,
            PointerTrg::Stack(_,_,_,_,_,_) => 3,
            PointerTrg::Aux(_) => 0,
            PointerTrg::AuxArray => 0
        }
    }
    fn elem_sort<Em : Embed>(&self,pos: usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        match *self {
            PointerTrg::Null => panic!("Invalid index"),
            PointerTrg::Global(_) => panic!("Invalid index"),
            PointerTrg::Heap(_,bw) => if pos==0 {
                em.tp_bitvec(bw)
            } else {
                panic!("Invalid index")
            },
            PointerTrg::Stack(_,thr_bw,_,fr_bw,_,alloc_bw) => match pos {
                0 => em.tp_bitvec(thr_bw),
                1 => em.tp_bitvec(fr_bw),
                2 => em.tp_bitvec(alloc_bw),
                _ => panic!("Invalid index")
            },
            PointerTrg::Aux(_) => unreachable!(),
            PointerTrg::AuxArray => unreachable!()
        }
    }
}

impl<'b> Composite for PointerTrg<'b> {
    fn combine<'a,Em,FComb,FL,FR>(x: OptRef<'a,Self>,y: OptRef<'a,Self>,
                                  inp_x: Transf<Em>,inp_y: Transf<Em>,
                                  comb: &FComb,_: &FL,_: &FR,em: &mut Em)
                                  -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>
        where Em : Embed,
              FComb : Fn(Transf<Em>,Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FL : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FR : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error> {

        let can_merge = match x.as_ref() {
            &PointerTrg::Null => match y.as_ref() {
                &PointerTrg::Null => true,
                _ => false
            },
            &PointerTrg::Global(ref glx) => match y.as_ref() {
                &PointerTrg::Global(ref gly) => glx==gly,
                _ => false
            },
            &PointerTrg::Heap(ref hp_x,bw_x) => match y.as_ref() {
                &PointerTrg::Heap(ref hp_y,bw_y) => hp_x==hp_y && bw_x==bw_y,
                _ => false
            },
            &PointerTrg::Stack((ref instr_x,ref fun_x),thr_bw_x,ref fr_x,fr_bw_x,ref call_x,call_bw_x)
                => match y.as_ref() {
                    &PointerTrg::Stack((ref instr_y,ref fun_y),thr_bw_y,ref fr_y,fr_bw_y,ref call_y,call_bw_y)
                        => instr_x==instr_y && fun_x==fun_y && thr_bw_x==thr_bw_y && fr_x==fr_y &&
                        fr_bw_x==fr_bw_y && call_x==call_y && call_bw_x==call_bw_y,
                    _ => false
                },
            &PointerTrg::Aux(aux_x) => match y.as_ref() {
                &PointerTrg::Aux(aux_y) => aux_x==aux_y,
                _ => false
            },
            &PointerTrg::AuxArray => match y.as_ref() {
                &PointerTrg::AuxArray => true,
                _ => false
            }
        };
        if can_merge {
            let ninp = comb(inp_x,inp_y,em)?;
            Ok(Some((x,ninp)))
        } else {
            Ok(None)
        }
    }
}

impl<'a> Pointer<'a> for BasePointer<'a> {
    fn from_pointer<'b,Em : Embed>(_: usize,
                                   base: OptRef<'b,BasePointer<'a>>,
                                   inp_base: Transf<Em>)
                                   -> (OptRef<'b,Self>,Transf<Em>) {
        (base,inp_base)
    }
    fn to_pointer<'b,Em : Embed>(ptr: OptRef<'b,Self>,
                                 inp_ptr: Transf<Em>)
                                 -> Option<(OptRef<'b,BasePointer<'a>>,Transf<Em>)> {
        Some((ptr,inp_ptr))
    }
    fn ptr_eq<Em : Embed>(lhs: &Self,
                          lhs_inp: Transf<Em>,
                          rhs: &Self,
                          rhs_inp: Transf<Em>)
                          -> Transf<Em> {
        lhs.eq(lhs_inp,rhs,rhs_inp)
    }
    fn ptr_lt<Em : Embed>(lhs: &Self,
                          lhs_inp: Transf<Em>,
                          rhs: &Self,
                          rhs_inp: Transf<Em>,
                          em: &mut Em)
                          -> Result<Transf<Em>,Em::Error> {
        let f = |&(ref ltrg,ref loff): &(PointerTrg<'a>,Offset),inp_l: Transf<Em>,&(ref rtrg,ref roff): &(PointerTrg<'a>,Offset),inp_r: Transf<Em>,em: &mut Em| {
            let lsz = ltrg.num_elem();
            let rsz = rtrg.num_elem();
            let ltrg_inp = Transformation::view(0,lsz,inp_l.clone());
            let rtrg_inp = Transformation::view(0,rsz,inp_r.clone());
            match comp_eq(ltrg,ltrg_inp,rtrg,rtrg_inp,em)? {
                None => Ok(None),
                Some(cond1) => {
                    let loff_inp = Transformation::view(lsz,inp_l.size()-lsz,inp_l);
                    let roff_inp = Transformation::view(rsz,inp_r.size()-lsz,inp_r);
                    match offset_lt(loff,loff_inp,roff,roff_inp,em)? {
                        None => Ok(None),
                        Some(cond2) => Ok(Some(Transformation::and(vec![cond1,
                                                                        cond2])))
                    }
                }
            }
        };
        lhs.compare_using(lhs_inp,rhs,rhs_inp,f,em)
    }
}

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash,Debug,Clone)]
pub enum PointerTrgMeaning {
    HeapSelector,
    ThreadSelector,
    FrameSelector,
    AllocSelector
}

impl<'a> Semantic for PointerTrg<'a> {
    type Meaning = PointerTrgMeaning;
    type MeaningCtx = ();
    fn meaning(&self,pos: usize) -> Self::Meaning {
        match self {
            &PointerTrg::Heap(_,_) if pos==0 => PointerTrgMeaning::HeapSelector,
            &PointerTrg::Stack(..) => match pos {
                0 => PointerTrgMeaning::ThreadSelector,
                1 => PointerTrgMeaning::FrameSelector,
                2 => PointerTrgMeaning::AllocSelector,
                _ => panic!("Index overflow")
            },
            _ => panic!("Index overflow")
        }
    }
    fn fmt_meaning<F : fmt::Write>(&self,m: &Self::Meaning,fmt: &mut F) -> Result<(),fmt::Error> {
        match m {
            &PointerTrgMeaning::HeapSelector => {
                write!(fmt,"heap_index")
            },
            &PointerTrgMeaning::ThreadSelector => {
                write!(fmt,"thread_index")
            },
            &PointerTrgMeaning::FrameSelector => {
                write!(fmt,"frame_index")
            },
            &PointerTrgMeaning::AllocSelector => {
                write!(fmt,"alloc_index")
            }
        }
    }
    fn first_meaning(&self) -> Option<(Self::MeaningCtx,Self::Meaning)> {
        match self {
            &PointerTrg::Heap(..) => Some(((),PointerTrgMeaning::HeapSelector)),
            &PointerTrg::Stack(..) => Some(((),PointerTrgMeaning::ThreadSelector)),
            _ => None
        }
    }
    fn next_meaning(&self,_: &mut Self::MeaningCtx,m: &mut Self::Meaning) -> bool {
        match m {
            &mut PointerTrgMeaning::HeapSelector => false,
            &mut PointerTrgMeaning::ThreadSelector => {
                *m = PointerTrgMeaning::FrameSelector;
                true
            },
            &mut PointerTrgMeaning::FrameSelector => {
                *m = PointerTrgMeaning::AllocSelector;
                true
            },
            &mut PointerTrgMeaning::AllocSelector => false
        }
    }
}

pub fn offset_eq<Em : Embed>(lhs: &Offset,lhs_inp: Transf<Em>,
                             rhs: &Offset,rhs_inp: Transf<Em>,
                             em: &mut Em)
                             -> Result<Option<Transf<Em>>,Em::Error> {
    let &(Data((lmult,loff)),ref ltp) = lhs;
    let &(Data((rmult,roff)),ref rtp) = rhs;
    match ltp {
        &None => match rtp {
            &None => if loff==roff {
                Ok(Some(Transformation::const_bool(true,em)?))
            } else {
                Ok(None)
            },
            &Some(_) => unimplemented!()
        },
        &Some(_) => unimplemented!()
    }
}

pub fn offset_lt<Em : Embed>(lhs: &Offset,lhs_inp: Transf<Em>,
                             rhs: &Offset,rhs_inp: Transf<Em>,
                             em: &mut Em)
                             -> Result<Option<Transf<Em>>,Em::Error> {
    let &(Data((lmult,loff)),ref ltp) = lhs;
    let &(Data((rmult,roff)),ref rtp) = rhs;
    match ltp {
        &None => match rtp {
            &None => if loff<roff {
                Ok(Some(Transformation::const_bool(true,em)?))
            } else {
                Ok(None)
            },
            &Some(_) => unimplemented!()
        },
        &Some(_) => unimplemented!()
    }
}

pub fn offset_le<Em : Embed>(lhs: &Offset,lhs_inp: Transf<Em>,
                             rhs: &Offset,rhs_inp: Transf<Em>,
                             em: &mut Em)
                             -> Result<Option<Transf<Em>>,Em::Error> {
    let &(Data((lmult,loff)),ref ltp) = lhs;
    let &(Data((rmult,roff)),ref rtp) = rhs;
    match ltp {
        &None => match rtp {
            &None => if loff<=roff {
                Ok(Some(Transformation::const_bool(true,em)?))
            } else {
                Ok(None)
            },
            &Some(_) => unimplemented!()
        },
        &Some(_) => unimplemented!()
    }
}

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash,Debug,Clone)]
pub struct BitField<T> {
    pub obj: T,
    size: Option<usize>
}

impl<T : HasSorts> HasSorts for BitField<T> {
    fn num_elem(&self) -> usize {
        match self.size {
            None => self.obj.num_elem(),
            Some(_) => self.obj.num_elem()+1
        }
    }
    fn elem_sort<Em : Embed>(&self,pos: usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        match self.size {
            None => self.obj.elem_sort(pos,em),
            Some(bw) => {
                let sz = self.obj.num_elem();
                if pos<sz {
                    self.obj.elem_sort(pos,em)
                } else {
                    em.tp_bitvec(bw)
                }
            }
        }
    }
}

impl<T : Composite> Composite for BitField<T> {
    fn combine<'a, Em, FComb, FL, FR>(
        this: OptRef<'a, Self>, 
        oth: OptRef<'a, Self>, 
        this_inp: Transf<Em>, 
        oth_inp: Transf<Em>, 
        comb: &FComb, 
        only_l: &FL, 
        only_r: &FR, 
        em: &mut Em
    ) -> Result<Option<(OptRef<'a, Self>, Transf<Em>)>, Em::Error>
        where
        Em: Embed,
        FComb: Fn(Transf<Em>, Transf<Em>, &mut Em) -> Result<Transf<Em>, Em::Error>,
        FL: Fn(Transf<Em>, &mut Em) -> Result<Transf<Em>, Em::Error>,
        FR: Fn(Transf<Em>, &mut Em) -> Result<Transf<Em>, Em::Error> {

        let (l_obj_inp,l_sz_inp) = match this.as_ref().size {
            None => (this_inp,None),
            Some(bw) => {
                let sz = this.as_ref().obj.num_elem();
                (Transformation::view(0,sz,this_inp.clone()),
                 Some((bw,Transformation::view(sz,1,this_inp))))
            }
        };
        let (r_obj_inp,r_sz_inp) = match oth.as_ref().size {
            None => (oth_inp,None),
            Some(bw) => {
                let sz = oth.as_ref().obj.num_elem();
                (Transformation::view(0,sz,oth_inp.clone()),
                 Some((bw,Transformation::view(sz,1,oth_inp))))
            }
        };
        let lobj = match this {
            OptRef::Ref(ref bf) => OptRef::Ref(&bf.obj),
            OptRef::Owned(bf) => OptRef::Owned(bf.obj)
        };
        let robj = match oth {
            OptRef::Ref(ref bf) => OptRef::Ref(&bf.obj),
            OptRef::Owned(bf) => OptRef::Owned(bf.obj)
        };
        match T::combine(lobj,robj,l_obj_inp,r_obj_inp,comb,only_l,only_r,em)? {
            None => Ok(None),
            Some((nobj,nobj_inp)) => match l_sz_inp {
                None => match r_sz_inp {
                    None => Ok(Some((OptRef::Owned(BitField { obj: nobj.as_obj(),
                                                              size: None }),
                                     nobj_inp))),
                    Some((rw,rbits)) => {
                        let nbits = only_r(rbits,em)?;
                        let ninp = Transformation::concat(&[nobj_inp,nbits]);
                        Ok(Some((OptRef::Owned(BitField { obj: nobj.as_obj(),
                                                          size: Some(rw) }),
                                 ninp)))
                    }
                },
                Some((lw,lbits)) => match r_sz_inp {
                    None => {
                        let nbits = only_l(lbits,em)?;
                        let ninp = Transformation::concat(&[nobj_inp,nbits]);
                        Ok(Some((OptRef::Owned(BitField { obj: nobj.as_obj(),
                                                          size: Some(lw) }),
                                 ninp)))
                    },
                    Some((rw,rbits)) => if lw==rw {
                        let nbits = comb(lbits,rbits,em)?;
                        let ninp = Transformation::concat(&[nobj_inp,nbits]);
                        Ok(Some((OptRef::Owned(BitField { obj: nobj.as_obj(),
                                                          size: Some(lw) }),
                                 ninp)))
                    } else {
                        Ok(None)
                    }
                }
            }
        }
    }
}

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash,Debug,Clone)]
pub enum BitFieldMeaning<M> {
    Obj(M),
    Field
}

impl<T : Semantic+HasSorts> Semantic for BitField<T> {
    type Meaning = BitFieldMeaning<T::Meaning>;
    type MeaningCtx = BitFieldMeaning<T::MeaningCtx>;
    fn meaning(&self,pos: usize) -> Self::Meaning {
        let sz = self.obj.num_elem();
        if pos<sz {
            BitFieldMeaning::Obj(self.obj.meaning(pos))
        } else {
            BitFieldMeaning::Field
        }
    }
    fn fmt_meaning<F : fmt::Write>(&self,m: &Self::Meaning,fmt: &mut F) -> Result<(),fmt::Error> {
        match m {
            &BitFieldMeaning::Obj(ref nm) => {
                write!(fmt,"obj.")?;
                self.obj.fmt_meaning(nm,fmt)
            },
            &BitFieldMeaning::Field => {
                write!(fmt,"bits")
            }
        }
    }
    fn first_meaning(&self) -> Option<(Self::MeaningCtx,Self::Meaning)> {
        match self.obj.first_meaning() {
            None => if self.size.is_some() {
                Some((BitFieldMeaning::Field,
                      BitFieldMeaning::Field))
            } else {
                None
            },
            Some((ctx,m)) => Some((BitFieldMeaning::Obj(ctx),
                                   BitFieldMeaning::Obj(m)))
        }
    }
    fn next_meaning(&self,ctx: &mut Self::MeaningCtx,m: &mut Self::Meaning) -> bool {
        let (nctx,nm) = match ctx {
            &mut BitFieldMeaning::Field => return false,
            &mut BitFieldMeaning::Obj(ref mut cctx) => match m {
                &mut BitFieldMeaning::Obj(ref mut cm) => if self.obj.next_meaning(cctx,cm) {
                    return true
                } else if self.size.is_some() {
                    (BitFieldMeaning::Field,
                     BitFieldMeaning::Field)
                } else {
                    return false
                },
                _ => unreachable!()
            }
        };
        *ctx = nctx;
        *m = nm;
        true
    }
}

impl<'b,Ptr : Pointer<'b>> Pointer<'b> for BitField<Ptr> {
    fn from_pointer<'a,Em : Embed>(bw: usize,
                                   ptr: OptRef<'a,BasePointer<'b>>,
                                   ptr_inp: Transf<Em>)
                                   -> (OptRef<'a,Self>,Transf<Em>) {
        let (nptr,nptr_inp) = Ptr::from_pointer(bw,ptr,ptr_inp);
        (OptRef::Owned(BitField { obj: nptr.as_obj(),
                                  size: None }),nptr_inp)
    }
    fn to_pointer<'a,Em : Embed>(this: OptRef<'a,Self>,inp: Transf<Em>)
                                 -> Option<(OptRef<'a,BasePointer<'b>>,Transf<Em>)> {
        let (obj,sz) = match this {
            OptRef::Ref(ref bf) => (OptRef::Ref(&bf.obj),bf.size),
            OptRef::Owned(bf) => (OptRef::Owned(bf.obj),bf.size)
        };
        let obj_inp = match sz {
            None => inp,
            Some(_) => {
                let sz = inp.size();
                Transformation::view(0,sz-1,inp)
            }
        };
        Ptr::to_pointer(obj,obj_inp)
    }
    fn ptr_eq<Em : Embed>(lhs: &Self,lhs_inp: Transf<Em>,
                          rhs: &Self,rhs_inp: Transf<Em>) -> Transf<Em> {
        let (lobj_inp,lsz) = match lhs.size {
            None => (lhs_inp,None),
            Some(w) => {
                let sz = lhs_inp.size();
                (Transformation::view(0,sz-1,lhs_inp.clone()),
                 Some((w,Transformation::view(sz-1,1,lhs_inp))))
            }
        };
        let (robj_inp,rsz) = match rhs.size {
            None => (rhs_inp,None),
            Some(w) => {
                let sz = rhs_inp.size();
                (Transformation::view(0,sz-1,rhs_inp.clone()),
                 Some((w,Transformation::view(sz-1,1,rhs_inp))))
            }
        };
        let base_eq = Ptr::ptr_eq(&lhs.obj,lobj_inp,
                                  &rhs.obj,robj_inp);
        match lsz {
            None => match rsz {
                None => base_eq,
                Some((rw,rbits)) => {
                    let f = move |_:&[Em::Expr],_:usize,e:Em::Expr,em:&mut Em| {
                        let bv0 = em.const_bitvec(rw,BigUint::from(0 as u8))?;
                        em.eq(e,bv0)
                    };
                    let sub_eq = Transformation::map_by_elem(Box::new(f),rbits);
                    Transformation::and(vec![base_eq,sub_eq])
                }
            },
            Some((lw,lbits)) => match rsz {
                None => {
                    let f = move |_:&[Em::Expr],_:usize,e:Em::Expr,em:&mut Em| {
                        let bv0 = em.const_bitvec(lw,BigUint::from(0 as u8))?;
                        em.eq(e,bv0)
                    };
                    let sub_eq = Transformation::map_by_elem(Box::new(f),lbits);
                    Transformation::and(vec![base_eq,sub_eq])
                },
                Some((rw,rbits)) => {
                    assert_eq!(rw,lw);
                    let f = |es:&[Em::Expr],em:&mut Em| em.eq(es[0].clone(),es[1].clone());
                    let sub_eq = Transformation::zips_by_elem(Box::new(f),vec![lbits,rbits]);
                    Transformation::and(vec![base_eq,sub_eq])
                }
            }
        }
    }
    fn ptr_lt<Em : Embed>(lhs: &Self,lhs_inp: Transf<Em>,
                          rhs: &Self,rhs_inp: Transf<Em>,em: &mut Em)
                          -> Result<Transf<Em>,Em::Error> {
        let (lobj_inp,lsz) = match lhs.size {
            None => (lhs_inp,None),
            Some(w) => {
                let sz = lhs_inp.size();
                (Transformation::view(0,sz-1,lhs_inp.clone()),
                 Some((w,Transformation::view(sz-1,1,lhs_inp))))
            }
        };
        let (robj_inp,rsz) = match rhs.size {
            None => (rhs_inp,None),
            Some(w) => {
                let sz = rhs_inp.size();
                (Transformation::view(0,sz-1,rhs_inp.clone()),
                 Some((w,Transformation::view(sz-1,1,rhs_inp))))
            }
        };
        let base_lt = Ptr::ptr_lt(&lhs.obj,lobj_inp,
                                  &rhs.obj,robj_inp,em)?;
        match lsz {
            None => match rsz {
                None => Ok(base_lt),
                _ => unimplemented!()
            },
            _ => unimplemented!()
        }
    }
}

impl<T : Bytes> Bytes for BitField<T> {
    fn byte_width(&self) -> usize {
        self.obj.byte_width()
    }
    fn extract_bytes<'a,Em : Embed>(this: OptRef<'a,Self>,inp: Transf<Em>,
                                    start: usize,len: usize,em: &mut Em)
                                    -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error> {
        Ok(None)
    }
    fn concat_bytes<'a,Em : Embed>(this: OptRef<'a,Self>,this_inp: Transf<Em>,
                                   oth: OptRef<'a,Self>,oth_inp: Transf<Em>,
                                   em: &mut Em)
                                   -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error> {
        Ok(None)
    }
}

pub fn ptr_sub<'a,Em : Embed,S>(lhs: &BasePointer<'a>,
                                lhs_inp: Transf<Em>,
                                rhs: &BasePointer<'a>,
                                rhs_inp: Transf<Em>,
                                tp: &SortKind<S>,
                                em: &mut Em)
                                -> Result<Transf<Em>,Em::Error> {
    let mut conds = Vec::new();
    let mut l_it = lhs.chosen(lhs_inp.clone());
    let mut ret : Option<Transf<Em>> = None;
    while let Some(l_view) = l_it.next(&mut conds,0,em)? {
        let (l_el,l_inp)
            = l_view.get_with_inp(lhs,lhs_inp.clone());
        let &(ref l_trg,ref l_off) = l_el;
        let l_trg_sz = l_trg.num_elem();
        let l_trg_inp = Transformation::view(0,l_trg_sz,
                                             l_inp.clone());
        let l_off_inp = Transformation::view(l_trg_sz,
                                             l_inp.size()-l_trg_sz,
                                             l_inp.clone());
        let &(Data((_,l_stat)),ref l_dyn) = l_off;
        let mut r_it = rhs.chosen(rhs_inp.clone());
        let cpos = conds.len();
        while let Some(r_view) = r_it.next(&mut conds,cpos,em)? {
            let (r_el,r_inp)
                = r_view.get_with_inp(rhs,rhs_inp.clone());
            let &(ref r_trg,ref r_off) = r_el;
            if *l_trg!=*r_trg {
                panic!("Pointer subtraction of pointers pointing to different objects");
            }
            let r_trg_sz = r_trg.num_elem();
            let r_trg_inp = Transformation::view(0,r_trg_sz,
                                                 r_inp.clone());
            let r_off_inp = Transformation::view(r_trg_sz,
                                                 r_inp.size()-r_trg_sz,
                                                 r_inp.clone());
            let &(Data((_,r_stat)),ref r_dyn) = r_off;
            if l_trg_sz!=0 {
                let f_eqs = |es:&[Em::Expr],em:&mut Em| {
                    em.eq(es[0].clone(),es[1].clone())
                };
                let eqs = Transformation::zips_by_elem(
                    Box::new(f_eqs),vec![l_trg_inp.clone(),
                                         r_trg_inp]);
                if l_trg_sz==1 {
                    conds.push(eqs);
                } else {
                    let f = |es:&[Em::Expr],res:&mut Vec<Em::Expr>,em:&mut Em| {
                        res.push(em.and(es.to_vec())?);
                        Ok(())
                    };
                    conds.push(Transformation::map(1,Box::new(f),eqs));
                }
            }
            match l_dyn {
                &None => match r_dyn {
                    &None => {
                        let rval = index_as_value(tp,l_stat-r_stat);
                        let re = em.embed(Expr::Const(rval))?;
                        let rtr = Transformation::constant(vec![re]);
                        ret = match ret {
                            None => Some(rtr),
                            Some(prev) => unimplemented!()
                        };
                    },
                    _ => unimplemented!()
                },
                _ => unimplemented!()
            }
        }
    }
    Ok(ret.unwrap())
}
