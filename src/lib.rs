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

#[macro_export]
macro_rules! __fx_values {
    ($func:expr, $($args:expr),+) => {
        itertools::izip!($($args),+).map($func).collect()
    };
}

#[macro_export]
macro_rules! __fx_tl {
    ($first:expr, $($_:expr),*) => {
        $first.timeline()
    };
}

#[macro_export]
/// Generic combination of `TimeSeries`
///
/// Will pairwise apply the function to the input `TimeSeries`. Is written as a
/// macro so that any number of arguments to the function can be used.
///
/// ### Inputs
/// * a function with 1 `Tuple` argument, containing `n` elements. The elements
/// must be provided by reference
/// * `n` futher `TimeSeries`. The types of the `TimeSeries` need not be the
/// same but they must match the signature of the function. The order of
/// the `TimeSeries` will be matched to the order of elements in the `Tuple`
///
/// ### Errors
/// Returns a Result as the input `TimeSeries` may not be the same length and
/// this will result in an error
///
/// ---
/// ### Example
/// ```
/// use timeseries::{TimeSeries, Timeline, DateRange, Period, Duration};
/// use timeseries::fx;
/// use time::{Date, Month};
/// let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
/// let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
/// let dr = DateRange::new(from, to);
/// let tl = Timeline::new(dr, Period::Quarter);
///
/// // Create two timeseries
/// let v1 = vec![1, 2, 3, 4];
/// let ts1 = TimeSeries::new(&tl, v1).unwrap();
/// let v2 = vec![5, 6, 7, 8];
/// let ts2 = TimeSeries::new(&tl, v2).unwrap();
///
/// // Write a generic function that can be pairwise applied to the elements
/// // of 2 TS and check OK
/// let op = |(&a, &b)| {
///     if a < 3 {
///         1
///     } else {
///         b + 1
///     }
/// };
///
/// let ts3 = fx!(op, &ts1, &ts2).unwrap();
/// assert_eq!(ts3.values(), &vec![1, 1, 8, 9]);
///
/// // Write a generic function that can be pairwise applied to the elements
/// // of 3 TS and check OK
/// let op2 = |(&a, &b, &c)| {
///     if a % 2 == 0 {
///         1
///     } else {
///         b + c
///     }
/// };
/// let ts4 = fx!(op2, &ts1, &ts2, &ts3).unwrap();
/// assert_eq!(ts4.values(), &vec![6, 1, 15, 1]);
/// ```
macro_rules! fx {
    ($func:expr, $($args:expr),+) => {
        TimeSeries::new(
            $crate::__fx_tl!($($args),+),
            $crate::__fx_values!($func, $($args.values()),+),
        )
    };
}

#[macro_export]
/// Generic combination of `TimeSeries`, using time
///
/// Will pairwise apply the function to the input `TimeSeries`. Is written as a
/// macro so that any number of arguments to the function can be used. This
/// function is time aware and allows the combining function to reference the
/// time period as part of evaluation
///
/// ### Inputs
/// * a function with 1 `Tuple` argument, containing `n + 1` elements. The
/// first element is a reference to time of the current period, which will be
/// provided as a `DateRange`. The `DateRange` must not be provided as reference,
/// whilst the following elements must be provided by reference
/// * `n` futher `TimeSeries`. The types of the `TimeSeries` need not be the
/// same but they must match the signature of the function. The order of
/// the `TimeSeries` will be matched to the order of elements in the `Tuple`
///
/// ### Errors
/// Returns a Result as the input `TimeSeries` may not be the same length and
/// this will result in an error
///
/// ---
/// ### Example
/// ```
/// use timeseries::{TimeSeries, Timeline, DateRange, Period, Duration};
/// use timeseries::fxt;
/// use time::{Date, Month};
/// let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
/// let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
/// let dr = DateRange::new(from, to);
/// let tl = Timeline::new(dr, Period::Quarter);
///
/// // Create two timeseries
/// let v1 = vec![1, 2, 3, 4];
/// let ts1 = TimeSeries::new(&tl, v1).unwrap();
/// let v2 = vec![5, 6, 7, 8];
/// let ts2 = TimeSeries::new(&tl, v2).unwrap();
///
/// // Create a date
/// let date = Date::from_calendar_date(2022, Month::May, 18).unwrap();
///
/// // Write a generic function that can be pairwise applied to the elements
/// // of 2 TS and check OK
/// // Need to specify types as Rust compiler cannot infer them
/// let op = |(t, &a, &b): (DateRange, &i32, &i32)| {
///     if t.contains(date) {
///         1000
///     }
///     else if a < 3 {
///         1
///     } else {
///         b + 1
///     }
/// };
///
/// let ts3 = fxt!(op, &ts1, &ts2);
/// assert!(ts3.is_ok());
/// let ts3 = ts3.unwrap();
/// assert_eq!(ts3.values(), &vec![1, 1000, 8, 9]);
/// ```
macro_rules! fxt {
    ($func:expr, $arg_first:expr, $($args_rest:expr),*) => {
        TimeSeries::new(
            $arg_first.timeline(),
            $crate::__fx_values!(
                $func,
                $arg_first.timeline(),
                $arg_first.values(),
                $($args_rest.values()),*
            ),
        )
    };
}
