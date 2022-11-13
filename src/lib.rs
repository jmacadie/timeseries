//! # ``TimeSeries`` library
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
//! This library builds upon the [`time`] library

#![warn(clippy::all, clippy::pedantic)]

mod date_arithmetic_ouput;
mod date_range;
mod duration;
mod error;
mod period;
mod time_series;
mod timeline;

pub use crate::date_arithmetic_ouput::DateArithmeticOutput;
pub use crate::date_range::DateRange;
pub use crate::duration::Duration;
pub use crate::error::TimeSeriesError;
pub use crate::period::Period;
pub use crate::time_series::AggType;
pub use crate::time_series::TimeSeries;
pub use crate::timeline::Timeline;
