use std::fmt;

use crate::Period;

#[derive(Debug, PartialEq, Eq)]
pub enum TimeSeriesError {
    TimelinesDoNotMatch,
    PeriodicityDoesNotMatch,
    TimelineDoesNotMatchValues,
    BadShift(Period),
    TimeDurationTooLarge,
    DateOutOfRange,
    AggregationTypeNotImplemented,
}

impl fmt::Display for TimeSeriesError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TimeSeriesError::TimelinesDoNotMatch => write!(f, "Timelines do not match"),
            TimeSeriesError::PeriodicityDoesNotMatch => {
                write!(f, "The periodicty of the two timelines does not match")
            }
            TimeSeriesError::TimelineDoesNotMatchValues => write!(
                f,
                "The length of the timeline is not the same as the length of the values"
            ),
            TimeSeriesError::BadShift(p) => match p {
                Period::Day => write!(f, "Shift provided can only contain days"),
                Period::Week => write!(f, "Shift provided must be a multiple of 7 days only"),
                Period::Month => write!(f, "Shift provided cannot contain days"),
                Period::Quarter => write!(f, "Shift provided isn't a whole number of quarters"),
                Period::Year => write!(f, "Shift provided isn't a whole number of years"),
            },
            TimeSeriesError::TimeDurationTooLarge => write!(
                f,
                "time::Duration too large. Can only hold values within i32"
            ),
            TimeSeriesError::DateOutOfRange => write!(f, "Operation creates a date out of range"),
            TimeSeriesError::AggregationTypeNotImplemented => {
                write!(f, "Aggregation type is not yet implemented")
            }
        }
    }
}

impl std::error::Error for TimeSeriesError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn print_em_out() {
        eprintln!("{}", TimeSeriesError::TimelinesDoNotMatch);
        eprintln!("{}", TimeSeriesError::PeriodicityDoesNotMatch);
        eprintln!("{}", TimeSeriesError::TimelineDoesNotMatchValues);
        eprintln!("{}", TimeSeriesError::BadShift(Period::Day));
        eprintln!("{}", TimeSeriesError::BadShift(Period::Week));
        eprintln!("{}", TimeSeriesError::BadShift(Period::Month));
        eprintln!("{}", TimeSeriesError::BadShift(Period::Quarter));
        eprintln!("{}", TimeSeriesError::BadShift(Period::Year));
        eprintln!("{}", TimeSeriesError::TimeDurationTooLarge);
        eprintln!("{}", TimeSeriesError::DateOutOfRange);
        eprintln!("{}", TimeSeriesError::AggregationTypeNotImplemented);
    }
}
