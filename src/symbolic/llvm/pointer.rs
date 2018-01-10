use smtrs::composite::*;
use smtrs::composite::choice::*;
use smtrs::composite::singleton::*;
use smtrs::composite::tuple::*;
use smtrs::composite::option::*;
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

pub trait Pointer<'a>: Composite<'a> {
    fn from_pointer<Em: Embed,P: Path<'a,Em,To=BasePointer<'a>>>(
        usize,&P,&P::From,&[Em::Expr],&mut Vec<Em::Expr>,&mut Em
    ) -> Result<Self,Em::Error>;
    fn to_pointer<Em: Embed,P: Path<'a,Em,To=Self>>(
        &P,&P::From,&[Em::Expr],&mut Vec<Em::Expr>,&mut Em
    ) -> Result<Option<BasePointer<'a>>,Em::Error>;
    fn ptr_eq<Em: Embed,P1: Path<'a,Em,To=Self>,P2: Path<'a,Em,To=Self>>(
        &P1,&P1::From,&[Em::Expr],
        &P2,&P2::From,&[Em::Expr],
        &mut Em
    ) -> Result<Em::Expr,Em::Error>;
    fn ptr_lt<Em: Embed,P1: Path<'a,Em,To=Self>,P2: Path<'a,Em,To=Self>>(
        &P1,&P1::From,&[Em::Expr],
        &P2,&P2::From,&[Em::Expr],
        &mut Em
    ) -> Result<Em::Expr,Em::Error>;
}

pub type BasePointer<'a> = Choice<(PointerTrg<'a>,Offset)>;

pub type Offset = (Data<(usize,usize)>,Option<Singleton>);

pub fn base_pointer_null<'a,Em: Embed>(
    res: &mut Vec<Em::Expr>,
    em: &mut Em)
    -> Result<BasePointer<'a>,Em::Error> {
    Choice::singleton((PointerTrg::Null,(Data((0,0)),None)),
                      &[][..],
                      res,em)
}

pub fn base_pointer_global<'a,Em: Embed>(
    mult: usize,
    name: &'a String,
    res: &mut Vec<Em::Expr>,
    em: &mut Em
) -> Result<BasePointer<'a>,Em::Error> {
    Choice::singleton((PointerTrg::Global(name),(Data((mult,0)),None)),
                      &[][..],
                      res,em)
}

/*
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
*/

pub fn offset_zero(sz: usize) -> Offset {
    (Data((0,sz)),None)
}

pub fn offset_advance<'a,Em: Embed,P: Path<'a,Em,To=Offset>>(
    path: &P,
    from: &mut P::From,
    _: &mut Vec<Em::Expr>,
    add: usize,
    _: &mut Em
) -> Result<(),Em::Error> {
    ((path.get_mut(from).0).0).1 += add;
    Ok(())
}

pub fn offset_advance_dyn<'a,Em: Embed,
                          POff: Path<'a,Em,To=Offset>,
                          PAdd: Path<'a,Em,To=Singleton>>(
    path: &POff,
    from: &mut POff::From,
    src:  &mut Vec<Em::Expr>,
    padd:     &PAdd,
    from_add: &PAdd::From,
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

impl<'a> Composite<'a> for PointerTrg<'a> {
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
    fn from_pointer<Em: Embed,P: Path<'a,Em,To=Self>>(
        bw: usize,
        path: &P,
        from: &P::From,
        src: &[Em::Expr],
        trg: &mut Vec<Em::Expr>,
        em: &mut Em
    ) -> Result<Self,Em::Error> {
        let base = path.get(from);
        path.read_into(from,0,base.num_elem(),src,trg,em)?;
        Ok(base.clone())
    }
    fn to_pointer<Em: Embed,P: Path<'a,Em,To=Self>>(
        path: &P,
        from: &P::From,
        src:  &[Em::Expr],
        trg:  &mut Vec<Em::Expr>,
        em:   &mut Em
    ) -> Result<Option<Self>,Em::Error> {
        let base = path.get(from);
        path.read_into(from,0,base.num_elem(),src,trg,em)?;
        Ok(Some(base.clone()))
    }
    fn ptr_eq<Em: Embed,P1: Path<'a,Em,To=Self>,P2: Path<'a,Em,To=Self>>(
        pl: &P1,froml: &P1::From,arrl: &[Em::Expr],
        pr: &P2,fromr: &P2::From,arrr: &[Em::Expr],
        em: &mut Em
    ) -> Result<Em::Expr,Em::Error> {
        match Choice::sym_eq(pl,froml,arrl,
                             pr,fromr,arrr,
                             em)? {
            Some(r) => Ok(r),
            None => em.const_bool(false)
        }
    }
    fn ptr_lt<Em: Embed,P1: Path<'a,Em,To=Self>,P2: Path<'a,Em,To=Self>>(
        pl: &P1,froml: &P1::From,arrl: &[Em::Expr],
        pr: &P2,fromr: &P2::From,arrr: &[Em::Expr],
        em: &mut Em
    ) -> Result<Em::Expr,Em::Error> {
        let f = |
        pl: &Then<P1,ChoiceEl<(PointerTrg<'a>,Offset)>>,
        froml: &P1::From,srcl: &[Em::Expr],
        pr: &Then<P2,ChoiceEl<(PointerTrg<'a>,Offset)>>,
        fromr: &P2::From,srcr: &[Em::Expr],
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
                 P1: Path<'a,Em,To=Offset>,
                 P2: Path<'a,Em,To=Offset>>(
    pl: &P1,froml: &P1::From,srcl: &[Em::Expr],
    pr: &P2,fromr: &P2::From,srcr: &[Em::Expr],
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
    pub fn obj() -> BitFieldObj<T> {
        BitFieldObj(PhantomData)
    }
    pub fn field<'a,Em: Embed,P: Path<'a,Em,To=Self>>(
        path: &P,
        from: &P::From,
        src:  &[Em::Expr],
        em:   &mut Em
    ) -> Result<Em::Expr,Em::Error> {
        debug_assert!(path.get(from).size.is_some());
        let off = path.get(from).obj.num_elem();
        path.read(from,off,src,em)
    }
}

pub struct BitFieldObj<T>(PhantomData<T>);

impl<T> Clone for BitFieldObj<T> {
    fn clone(&self) -> Self {
        BitFieldObj(PhantomData)
    }
}

impl<'a,T: 'a> SimplePathEl<'a> for BitFieldObj<T> {
    type From = BitField<T>;
    type To = T;
    fn get<'b>(&self,from: &'b Self::From) -> &'b Self::To where 'a: 'b {
        &from.obj
    }
    fn get_mut<'b>(&self,from: &'b mut Self::From) -> &'b mut Self::To where 'a: 'b {
        &mut from.obj
    }
}

impl<'a,Em: Embed,T: 'a> PathEl<'a,Em> for BitFieldObj<T> {
    fn read<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        from: &Prev::From,
        pos: usize,
        src: &[Em::Expr],
        em: &mut Em
    ) -> Result<Em::Expr,Em::Error> {
        prev.read(from,pos,src,em)
    }
    fn read_slice<'b,Prev: Path<'a,Em,To=Self::From>>(
        &self,prev: &Prev,from: &Prev::From,pos: usize,len: usize,src: &'b [Em::Expr])
        -> Option<&'b [Em::Expr]> {

        prev.read_slice(from,pos,len,src)
    }
    fn write<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        from: &Prev::From,
        pos: usize,
        expr: Em::Expr,
        src: &mut Vec<Em::Expr>,
        em: &mut Em
    ) -> Result<(),Em::Error> {
        prev.write(from,pos,expr,src,em)
    }
    fn write_slice<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        from: &mut Prev::From,
        pos: usize,
        old_len: usize,
        src: &mut Vec<Em::Expr>,
        trg: &mut Vec<Em::Expr>,
        em: &mut Em
    ) -> Result<(),Em::Error> {
        prev.write_slice(from,pos,old_len,src,trg,em)
    }
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

impl<'a,T: Composite<'a>> Composite<'a> for BitField<T> {
    fn combine<Em,PL,PR,FComb,FL,FR>(
        pl: &PL,froml: &PL::From,srcl: &[Em::Expr],
        pr: &PR,fromr: &PR::From,srcr: &[Em::Expr],
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

        let pobjl = pl.clone().then(BitField::obj());
        let pobjr = pr.clone().then(BitField::obj());

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

/*impl<'b,Ptr : Pointer<'b>> Pointer<'b> for BitField<Ptr> {
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
*/
