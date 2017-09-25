extern crate smtrs;

use self::smtrs::composite::*;
use self::smtrs::embed::{Embed};
use super::{InstructionRef};
use super::frame::{FrameId,ContextId};
use super::program::{ThreadId};

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash,Clone)]
pub enum Error<'a> {
    NullPointerDeref,
    UnknownGlobal(&'a String),
    UnknownHeapLocation(InstructionRef<'a>),
    UnknownHeapIndex(InstructionRef<'a>),
    UnknownThread(ThreadId<'a>),
    UnknownThreadIndex(ThreadId<'a>),
    UnknownFrameId(FrameId<'a>),
    UnknownAllocaInstr(InstructionRef<'a>),
    UnknownAllocaIndex(InstructionRef<'a>)
}

pub type Errors<'a> = Assoc<Error<'a>,SingletonBool>;

pub fn add_error<'a,'b,Em>(errs: OptRef<'a,Errors<'b>>,inp_errs: Transf<Em>,err: &Error<'b>,em: &mut Em)
                           -> Result<(OptRef<'a,Errors<'b>>,Transf<Em>),Em::Error>
    where Em : Embed {
    let cond = em.const_bool(true)?;
    let inp_cond = Transformation::constant(vec![cond]);
    assoc_insert(errs,inp_errs,err,
                 OptRef::Ref(&BOOL_SINGLETON),inp_cond)
}
