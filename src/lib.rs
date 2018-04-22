// TODO remove this
#![allow(dead_code)]

extern crate lalrpop_util;

mod eval;
pub mod untyped;
pub mod conversion;
mod readable;
mod substitution;

// need to internalize this
mod typed;
mod type_system;

pub mod parsers;

