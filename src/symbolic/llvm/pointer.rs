extern crate smtrs;

use self::smtrs::composite::*;
use self::smtrs::embed::Embed;
use self::smtrs::types::SortKind;
use super::{InstructionRef};
use super::frame::{FrameId};
use super::program::{ThreadId};

pub trait Pointer<'b> : Composite {
    fn from_pointer<'a,Em : Embed>(usize,OptRef<'a,BasePointer<'b>>,Transf<Em>) -> (OptRef<'a,Self>,Transf<Em>);
    fn to_pointer<'a,Em : Embed>(OptRef<'a,Self>,Transf<Em>) -> Option<(OptRef<'a,BasePointer<'b>>,Transf<Em>)>;
}

pub type BasePointer<'a> = Choice<(PointerTrg<'a>,Offset)>;

pub type Offset = (Data<(usize,usize)>,Option<Singleton>);

pub fn base_pointer_global<'a,'b,Em>(name: &'a String,em: &mut Em)
                                     -> Result<(BasePointer<'a>,
                                                Transf<Em>),Em::Error>
    where Em : Embed {
    let (ch0,inp_ch0) = choice_empty();
    let (ch,inp_ch) = choice_insert(OptRef::Owned(ch0),inp_ch0,Transformation::const_bool(true,em)?,
                                    OptRef::Owned((PointerTrg::Global(name),
                                                   (Data((0,0)),None))),
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
                _ => panic!("Invalid offset type")
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
          InstructionRef<'a>,usize)            // Allocation selector
}

impl<'b> Composite for PointerTrg<'b> {
    fn num_elem(&self) -> usize {
        match *self {
            PointerTrg::Null => 0,
            PointerTrg::Global(_) => 0,
            PointerTrg::Heap(_,_) => 1,
            PointerTrg::Stack(_,_,_,_,_,_) => 3
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
            }
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

}
