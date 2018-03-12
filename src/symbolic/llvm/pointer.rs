use smtrs::composite::*;
use smtrs::composite::choice::*;
use smtrs::composite::singleton::*;
use smtrs::composite::tuple::*;
use smtrs::composite::option::*;
use smtrs::composite::vec::*;
use smtrs::embed::Embed;
use smtrs::types::{Sort,SortKind};
use smtrs::expr::Expr;
use super::{InstructionRef};
use super::frame::{FrameId};
use super::program::{ThreadId};
use num_bigint::BigUint;
use super::mem::Bytes;
use std::fmt;
use std::marker::PhantomData;

pub trait Pointer<'a>: 'a+Composite<'a> {
    fn from_pointer<Em: Embed,From,P: Path<'a,Em,From,To=BasePointer<'a>>>(
        usize,&P,&From,&[Em::Expr],&mut Vec<Em::Expr>,&mut Em
    ) -> Result<Self,Em::Error>;
    fn to_pointer<Em: Embed,From,P: Path<'a,Em,From,To=Self>>(
        &P,&From,&[Em::Expr],&mut Vec<Em::Expr>,&mut Em
    ) -> Result<Option<BasePointer<'a>>,Em::Error>;
    fn ptr_eq<Em: Embed,
              From1,P1: Path<'a,Em,From1,To=Self>,
              From2,P2: Path<'a,Em,From2,To=Self>>(
        &P1,&From1,&[Em::Expr],
        &P2,&From2,&[Em::Expr],
        &mut Em
    ) -> Result<Em::Expr,Em::Error>;
    fn ptr_lt<Em: Embed,
              From1,P1: Path<'a,Em,From1,To=Self>,
              From2,P2: Path<'a,Em,From2,To=Self>>(
        &P1,&From1,&[Em::Expr],
        &P2,&From2,&[Em::Expr],
        &mut Em
    ) -> Result<Em::Expr,Em::Error>;
}

pub type BasePointer<'a> = Choice<(PointerTrg<'a>,Offset)>;

pub type Offset = (Data<(usize,usize)>,Option<Singleton>);

pub fn base_pointer_null<'a,Em: Embed>(
    res: &mut Vec<Em::Expr>,
    em: &mut Em)
    -> Result<BasePointer<'a>,Em::Error> {
    Choice::singleton(|res,em| { Ok((PointerTrg::Null,(Data((0,0)),None))) },
                      res,em)
}

pub fn base_pointer_global<'a,Em: Embed>(
    mult: usize,
    name: &'a String,
    res: &mut Vec<Em::Expr>,
    em: &mut Em
) -> Result<BasePointer<'a>,Em::Error> {
    Choice::singleton(|res,em| { Ok((PointerTrg::Global(name),(Data((mult,0)),None))) },
                      res,em)
}

pub fn base_pointer_gep<'a,Em: Embed,
                        From,P: Path<'a,Em,From,To=BasePointer<'a>>,
                        FromGEP,PGEP: Path<'a,Em,FromGEP,To=CompVec<(Option<Singleton>,Data<usize>)>>>(
    p: P,
    from: &mut From,
    arr: &mut Vec<Em::Expr>,
    gep: &PGEP,
    gep_from: &FromGEP,
    gep_arr: &[Em::Expr],
    em: &mut Em)
    -> Result<(),Em::Error> {
    for el in Choice::elements(p,from) {
        let off = el.then(element2of2());
        for gep_el in CompVec::elements(gep.clone(),gep_from) {
            let dyn = gep_el.clone().then(element1of2());
            let stat = gep_el.then(element2of2()).get(gep_from).0;
            match option(dyn,gep_from) {
                None => offset_advance(&off,from,arr,stat,em)?,
                Some(rdyn) => if !offset_advance_dyn(&off,from,arr,&rdyn,gep_from,gep_arr,em)? {
                    panic!("Cannot advance pointer dynamically here")
                }
            }
        }
    }
    Ok(())
}

pub fn offset_zero(sz: usize) -> Offset {
    (Data((0,sz)),None)
}

pub fn offset_advance<'a,Em: Embed,From,P: Path<'a,Em,From,To=Offset>>(
    path: &P,
    from: &mut From,
    _: &mut Vec<Em::Expr>,
    add: usize,
    _: &mut Em
) -> Result<(),Em::Error> {
    ((path.get_mut(from).0).0).1 += add;
    Ok(())
}

pub fn offset_advance_dyn<'a,Em: Embed,
                          FromOff,POff: Path<'a,Em,FromOff,To=Offset>,
                          FromAdd,PAdd: Path<'a,Em,FromAdd,To=Singleton>>(
    path: &POff,
    from: &mut FromOff,
    src:  &mut Vec<Em::Expr>,
    padd:     &PAdd,
    from_add: &FromAdd,
    src_add:  &[Em::Expr],
    em: &mut Em
) -> Result<bool,Em::Error> {
    let add = padd.get(from_add);
    let has_offset = match path.get(from).1 {
        Some(ref tp) => if *tp==*add {
            true
        } else {
            return Ok(false)
        },
        None => false
    };
    if has_offset {
        let path_off = path.clone().then(element2of2()).then(some());
        let off_e = Singleton::get(&path_off,from,src,em)?;
        let add_e = Singleton::get(padd,from_add,src_add,em)?;
        let tp = em.type_of(&off_e)?;
        let ne = match em.unbed_sort(&tp)? {
            SortKind::Int => em.add_int(vec![off_e,add_e])?,
            SortKind::BitVec(_) => em.bvadd(off_e,add_e)?,
            _ => panic!("Invalid offset type: {:?}",tp)
        };
        Singleton::set_same_type(&path_off,from,src,ne,em)?;
        Ok(true)
    } else {
        let path_off = path.clone().then(element2of2());
        set_some(&path_off,from,src,padd,from_add,src_add,em)?;
        Ok(true)
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

impl<'a> PointerTrg<'a> {
    pub fn null<Em: Embed>(_: &mut Vec<Em::Expr>,_: &mut Em) -> Result<Self,Em::Error> {
        Ok(PointerTrg::Null)
    }
    pub fn global<Em: Embed>(name: &'a String,_: &mut Vec<Em::Expr>,_: &mut Em) -> Result<Self,Em::Error> {
        Ok(PointerTrg::Global(name))
    }
    pub fn heap<Em: Embed>(instr: InstructionRef<'a>,
                           idx: Em::Expr,
                           arr: &mut Vec<Em::Expr>,
                           em: &mut Em) -> Result<Self,Em::Error> {
        let idx_tp = em.type_of(&idx)?;
        let bw = match em.unbed_sort(&idx_tp)? {
            SortKind::BitVec(r) => r,
            _ => panic!("Heap pointer created with non-bitvec index")
        };
        arr.push(idx);
        Ok(PointerTrg::Heap(instr,bw))
    }
    pub fn stack<Em: Embed>(thr: ThreadId<'a>,
                            thr_idx: Em::Expr,
                            fr: FrameId<'a>,
                            fr_idx: Em::Expr,
                            alloc: InstructionRef<'a>,
                            alloc_idx: Em::Expr,
                            res: &mut Vec<Em::Expr>,
                            em: &mut Em) -> Result<Self,Em::Error> {
        let thr_tp = em.type_of(&thr_idx)?;
        let thr_bw = em.is_bitvec(&thr_tp)?
        .expect("Stack pointer created with non-bitvec thread-index");
        let fr_tp = em.type_of(&fr_idx)?;
        let fr_bw = em.is_bitvec(&fr_tp)?
        .expect("Stack pointer created with non-bitvec frame-index");
        let alloc_tp = em.type_of(&alloc_idx)?;
        let alloc_bw = em.is_bitvec(&alloc_tp)?
        .expect("Stack pointer created with non-bitvec alloc-index");
        res.reserve(3);
        res.push(thr_idx);
        res.push(fr_idx);
        res.push(alloc_idx);
        Ok(PointerTrg::Stack(thr,thr_bw,
                             fr,fr_bw,
                             alloc,alloc_bw))
    }
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
    fn elem_sort<Em: Embed>(&self,pos: usize,em: &mut Em)
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

impl<'a> Composite<'a> for PointerTrg<'a> {
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

        let ptrl = pl.get(froml);
        let ptrr = pr.get(fromr);

        if *ptrl==*ptrr {
            for i in 0..ptrl.num_elem() {
                let ne = comb(pl.read(froml,i,arrl,em)?,
                              pr.read(fromr,i,arrr,em)?,
                              em)?;
                res.push(ne);
            }
            Ok(Some(ptrl.clone()))
        } else {
            Ok(None)
        }
    }
}

impl<'a> Pointer<'a> for BasePointer<'a> {
    fn from_pointer<Em: Embed,From,P: Path<'a,Em,From,To=Self>>(
        bw: usize,
        path: &P,
        from: &From,
        src: &[Em::Expr],
        trg: &mut Vec<Em::Expr>,
        em: &mut Em
    ) -> Result<Self,Em::Error> {
        let base = path.get(from);
        path.read_into(from,0,base.num_elem(),src,trg,em)?;
        Ok(base.clone())
    }
    fn to_pointer<Em: Embed,From,P: Path<'a,Em,From,To=Self>>(
        path: &P,
        from: &From,
        src:  &[Em::Expr],
        trg:  &mut Vec<Em::Expr>,
        em:   &mut Em
    ) -> Result<Option<Self>,Em::Error> {
        let base = path.get(from);
        path.read_into(from,0,base.num_elem(),src,trg,em)?;
        Ok(Some(base.clone()))
    }
    fn ptr_eq<Em: Embed,
              From1,P1: Path<'a,Em,From1,To=Self>,
              From2,P2: Path<'a,Em,From2,To=Self>>(
        pl: &P1,froml: &From1,arrl: &[Em::Expr],
        pr: &P2,fromr: &From2,arrr: &[Em::Expr],
        em: &mut Em
    ) -> Result<Em::Expr,Em::Error> {
        match Choice::sym_eq(pl,froml,arrl,
                             pr,fromr,arrr,
                             em)? {
            Some(r) => Ok(r),
            None => em.const_bool(false)
        }
    }
    fn ptr_lt<Em: Embed,
              From1,P1: Path<'a,Em,From1,To=Self>,
              From2,P2: Path<'a,Em,From2,To=Self>>(
        pl: &P1,froml: &From1,arrl: &[Em::Expr],
        pr: &P2,fromr: &From2,arrr: &[Em::Expr],
        em: &mut Em
    ) -> Result<Em::Expr,Em::Error> {
        let f = |
        pl: &Then<P1,ChoiceEl>,
        froml: &From1,srcl: &[Em::Expr],
        pr: &Then<P2,ChoiceEl>,
        fromr: &From2,srcr: &[Em::Expr],
        em: &mut Em| {

            let &(ref trgl,ref offl) = pl.get(froml);
            let &(ref trgr,ref offr) = pr.get(fromr);

            if *trgl!=*trgr {
                return Ok(None)
            }
            
            let poffl = pl.clone().then(element2of2());
            let poffr = pr.clone().then(element2of2());
            if let Some(cond_lt) = offset_lt(&poffl,froml,srcl,
                                             &poffr,fromr,srcr,em)? {
                let sz = trgl.num_elem();  
                let mut conj = Vec::with_capacity(sz+1);
                conj.push(cond_lt);
            
                for i in 0..sz {
                    let le = pl.read(froml,i,srcl,em)?;
                    let re = pr.read(fromr,i,srcr,em)?;
                    let eq = em.eq(le,re)?;
                    conj.push(eq);
                }
                let res = em.and(conj)?;
                Ok(Some(res))
            } else {
                Ok(None)
            }
        };
        match Choice::compare_using(pl,froml,arrl,
                                    pr,fromr,arrr,f,em)? {
            None => em.const_bool(false),
            Some(res) => Ok(res)
        }
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
/*
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
}*/

pub fn offset_lt<'a,Em: Embed,
                 From1,P1: Path<'a,Em,From1,To=Offset>,
                 From2,P2: Path<'a,Em,From2,To=Offset>>(
    pl: &P1,froml: &From1,srcl: &[Em::Expr],
    pr: &P2,fromr: &From2,srcr: &[Em::Expr],
    em: &mut Em
) -> Result<Option<Em::Expr>,Em::Error> {
    
    let &(Data((lmult,loff)),ref ltp) = pl.get(froml);
    let &(Data((rmult,roff)),ref rtp) = pr.get(fromr);
    match ltp {
        &None => match rtp {
            &None => if loff<roff {
                let res = em.const_bool(true)?;
                Ok(Some(res))
            } else {
                Ok(None)
            },
            &Some(_) => unimplemented!()
        },
        &Some(_) => unimplemented!()
    }
}

/*
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
*/
#[derive(PartialEq,Eq,PartialOrd,Ord,Hash,Debug,Clone)]
pub struct BitField<T> {
    pub obj: T,
    size: Option<usize>
}

impl<T: HasSorts> BitField<T> {
    pub fn obj() -> BitFieldObj {
        BitFieldObj
    }
    pub fn field<'a,Em: Embed,From,P: Path<'a,Em,From,To=Self>>(
        path: &P,
        from: &From,
        src:  &[Em::Expr],
        em:   &mut Em
    ) -> Result<Em::Expr,Em::Error>
        where T: 'a {
        debug_assert!(path.get(from).size.is_some());
        let off = path.get(from).obj.num_elem();
        path.read(from,off,src,em)
    }
    pub fn field_opt<'a,Em: Embed,From,P: Path<'a,Em,From,To=Self>>(
        path: &P,
        from: &From,
        src:  &[Em::Expr],
        em:   &mut Em
    ) -> Result<Option<(Em::Expr,usize)>,Em::Error>
    where T: 'a {
        match path.get(from).size {
            None => Ok(None),
            Some(bw) => {
                let off = path.get(from).obj.num_elem();
                let expr = path.read(from,off,src,em)?;
                Ok(Some((expr,bw)))
            }
        }
    }
}

#[derive(Clone)]
pub struct BitFieldObj;

impl<'a,T: 'a> SimplePathEl<'a,BitField<T>> for BitFieldObj {
    type To = T;
    fn get<'b>(&self,from: &'b BitField<T>) -> &'b Self::To where 'a: 'b {
        &from.obj
    }
    fn get_mut<'b>(&self,from: &'b mut BitField<T>)
                   -> &'b mut Self::To where 'a: 'b {
        &mut from.obj
    }
}

impl<'a,Em: Embed,T: 'a> PathEl<'a,Em,BitField<T>> for BitFieldObj {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=BitField<T>>>(
        &self,
        prev: &Prev,
        from: &PrevFrom,
        pos: usize,
        src: &[Em::Expr],
        em: &mut Em
    ) -> Result<Em::Expr,Em::Error> {
        prev.read(from,pos,src,em)
    }
    fn read_slice<'b,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=BitField<T>>>(
        &self,prev: &Prev,from: &PrevFrom,pos: usize,len: usize,src: &'b [Em::Expr])
        -> Option<&'b [Em::Expr]> {

        prev.read_slice(from,pos,len,src)
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=BitField<T>>>(
        &self,
        prev: &Prev,
        from: &PrevFrom,
        pos: usize,
        expr: Em::Expr,
        src: &mut Vec<Em::Expr>,
        em: &mut Em
    ) -> Result<(),Em::Error> {
        prev.write(from,pos,expr,src,em)
    }
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=BitField<T>>>(
        &self,
        prev: &Prev,
        from: &mut PrevFrom,
        pos: usize,
        old_len: usize,
        src: &mut Vec<Em::Expr>,
        trg: &mut Vec<Em::Expr>,
        em: &mut Em
    ) -> Result<(),Em::Error> {
        prev.write_slice(from,pos,old_len,src,trg,em)
    }
}

impl<T: HasSorts> HasSorts for BitField<T> {
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

impl<'a,T: Composite<'a>> Composite<'a> for BitField<T> {
    fn combine<Em,FromL,PL,FromR,PR,FComb,FL,FR>(
        pl: &PL,froml: &FromL,srcl: &[Em::Expr],
        pr: &PR,fromr: &FromR,srcr: &[Em::Expr],
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

        let pobjl = then(pl.clone(),BitFieldObj);
        let pobjr = then(pr.clone(),BitFieldObj);

        let nobj = match T::combine(&pobjl,froml,srcl,
                                    &pobjr,fromr,srcr,
                                    comb,only_l,only_r,
                                    res,em)? {
            None => return Ok(None),
            Some(r) => r
        };

        let nsize = match pl.get(froml).size {
            None => match pr.get(fromr).size {
                None => None,
                Some(szr) => {
                    let fieldr = BitField::field(pr,fromr,srcr,em)?;
                    let nfield = only_r(fieldr,em)?;
                    res.push(nfield);
                    Some(szr)
                }
            },
            Some(szl) => match pr.get(fromr).size {
                None => {
                    let fieldl = BitField::field(pl,froml,srcl,em)?;
                    let nfield = only_l(fieldl,em)?;
                    res.push(nfield);
                    Some(szl)
                },
                Some(szr) => if szl==szr {
                    let fieldl = BitField::field(pl,froml,srcl,em)?;
                    let fieldr = BitField::field(pr,fromr,srcr,em)?;
                    let nfield = comb(fieldl,fieldr,em)?;
                    res.push(nfield);
                    Some(szl)
                } else {
                    return Ok(None)
                }
            }
        };
        Ok(Some(BitField { obj: nobj,
                           size: nsize }))
    }
}

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash,Debug,Clone)]
pub enum BitFieldMeaning<M> {
    Obj(M),
    Field
}

impl<T: Semantic+HasSorts> Semantic for BitField<T> {
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

impl<'a,Ptr: Pointer<'a>> Pointer<'a> for BitField<Ptr> {
    fn from_pointer<Em: Embed,From,P: Path<'a,Em,From,To=BasePointer<'a>>>(
        bw: usize,path: &P,from: &From,inp: &[Em::Expr],
        res: &mut Vec<Em::Expr>,em: &mut Em
    ) -> Result<Self,Em::Error> {
        let nptr = Ptr::from_pointer(bw,path,from,inp,res,em)?;
        Ok(BitField { obj: nptr,
                      size: None })
    }
    fn to_pointer<Em: Embed,From,P: Path<'a,Em,From,To=Self>>(
        path: &P,from: &From,inp: &[Em::Expr],
        res: &mut Vec<Em::Expr>,em: &mut Em
    ) -> Result<Option<BasePointer<'a>>,Em::Error> {
        Ptr::to_pointer(&then(path.clone(),
                              BitFieldObj),
                        from,inp,res,em)
    }
    fn ptr_eq<Em: Embed,
              From1,P1: Path<'a,Em,From1,To=Self>,
              From2,P2: Path<'a,Em,From2,To=Self>>(
        path1: &P1,from1: &From1,inp1: &[Em::Expr],
        path2: &P2,from2: &From2,inp2: &[Em::Expr],
        em: &mut Em
    ) -> Result<Em::Expr,Em::Error> {
        let base_eq = Ptr::ptr_eq(&then(path1.clone(),
                                        BitFieldObj),
                                  from1,inp1,
                                  &then(path2.clone(),
                                        BitFieldObj),
                                  from2,inp2,em)?;
        let field1 = BitField::field_opt(path1,from1,inp1,em)?;
        let field2 = BitField::field_opt(path2,from2,inp2,em)?;
        match field1 {
            None => match field2 {
                None => Ok(base_eq),
                Some((e2,bw2)) => {
                    let bv0 = em.const_bitvec(bw2,BigUint::from(0u8))?;
                    let field_zero = em.eq(e2,bv0)?;
                    em.and(vec![base_eq,field_zero])
                }
            },
            Some((e1,bw1)) => match field2 {
                None => {
                    let bv0 = em.const_bitvec(bw1,BigUint::from(0u8))?;
                    let field_zero = em.eq(e1,bv0)?;
                    em.and(vec![base_eq,field_zero])
                },
                Some((e2,bw2)) => {
                    assert_eq!(bw1,bw2);
                    let field_eq = em.eq(e1,e2)?;
                    em.and(vec![base_eq,field_eq])
                }
            }
        }
    }
    fn ptr_lt<Em: Embed,
              From1,P1: Path<'a,Em,From1,To=Self>,
              From2,P2: Path<'a,Em,From2,To=Self>>(
        path1: &P1,from1: &From1,inp1: &[Em::Expr],
        path2: &P2,from2: &From2,inp2: &[Em::Expr],
        em: &mut Em
    ) -> Result<Em::Expr,Em::Error> {
        let base_lt = Ptr::ptr_lt(&then(path1.clone(),
                                        BitFieldObj),
                                  from1,inp1,
                                  &then(path2.clone(),
                                        BitFieldObj),
                                  from2,inp2,em)?;
        let field1 = BitField::field_opt(path1,from1,inp1,em)?;
        let field2 = BitField::field_opt(path2,from2,inp2,em)?;
        match field1 {
            None => match field2 {
                None => Ok(base_lt),
                _ => unimplemented!()
            },
            _ => unimplemented!()
        }
    }
}

impl<'a,T: 'a+Bytes<'a>> Bytes<'a> for BitField<T> {
    fn byte_width(&self) -> usize {
        self.obj.byte_width()
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

pub fn ptr_sub<'a,Em: Embed,S,
               FromL,PL: Path<'a,Em,FromL,To=BasePointer<'a>>,
               FromR,PR: Path<'a,Em,FromR,To=BasePointer<'a>>>(

    pl: &PL,froml: &FromL,inpl: &[Em::Expr],
    pr: &PR,fromr: &FromR,inpr: &[Em::Expr],
    tp: &SortKind<S>,em: &mut Em) -> Result<Em::Expr,Em::Error> {

    let mut conds = Vec::new();
    let mut l_it = Choice::choices(pl.clone(),froml,inpl,em)?;
    let mut ret: Option<Em::Expr> = None;
    while let Some(l) = l_it.next(&mut conds,0,em)? {

        let l_trg = then(l.clone(),Element1Of2);
        let l_off = then(l,Element2Of2);

        let &(Data((_,l_stat)),_) = l_off.get(froml);
        let mut r_it = Choice::choices(pr.clone(),fromr,inpr,em)?;
        let cpos = conds.len();
        while let Some(r) = r_it.next(&mut conds,cpos,em)? {
            let r_trg = then(r.clone(),Element1Of2);
            let r_off = then(r,Element2Of2);

            if *l_trg.get(froml)!=*r_trg.get(fromr) {
                panic!("Pointer subtraction of pointers pointing to different objects");
            }
            let &(Data((_,r_stat)),_) = r_off.get(fromr);

            match option(then(l_off.clone(),Element2Of2),froml) {
                None => match option(then(r_off,Element2Of2),fromr) {
                    None => {
                        let rval = index_as_value(tp,l_stat-r_stat);
                        let re = em.value(rval)?;
                        ret = match ret {
                            None => Some(re),
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
