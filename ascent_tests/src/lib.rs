// #![allow(warnings)]
// #![feature(decl_macro)]
#![feature(macro_metavar_expr)]
#![allow(unused_imports)]
#![allow(confusable_idents)]

mod ascent_maybe_par;
mod tests;
pub mod utils;
mod se;
mod exps;
mod analysis_exp;
mod agg_tests;
mod example_tests;
mod macros_tests;
pub mod capture_generic;
mod capture_turbofish_tests;

mod provenance;
mod semiring_manual;
mod semiring_auto;
mod semiring_correctness;
mod dynamic_programming;
mod incremental;
mod extdb;
mod graph;
mod io;
mod sat;
