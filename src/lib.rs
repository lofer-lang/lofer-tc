// TODO remove this
#![allow(dead_code)]

extern crate lalrpop_util;

mod eval;
pub mod untyped;
mod conversion;
mod readable;
mod substitution;

// need to internalize this
mod typed;
mod type_system;

mod parsers;

