//! # TimeSeries library
//! 
//! Provides a framework within which to build time aware projection
//! models in Rust. The library is written to work with time periods
//! of daily through to annual, with the primary focus being on
//! intervals of a month and upwards
//! 
//! This model style is inspired by financial models in Excel and is
//! intended to provide a way of creating and running those types of
//! model in Rust
//! 
//! This library builds upon the [`time`][#time] library
//! 
//! [#time]: https://docs.rs/time/0.3.6/time/
mod timeline;
mod date_range;
mod period;
mod time_series;

pub use crate::date_range::DateRange;
pub use crate::timeline::Timeline;
pub use crate::period::Period;
