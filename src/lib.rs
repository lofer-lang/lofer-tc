// TODO remove this
#![allow(dead_code)]

extern crate lalrpop_util;

mod eval;
mod untyped;
mod conversion;
mod readable;
mod substitution;

// need to internalize this
mod typed;
mod type_system;

mod parsers;

