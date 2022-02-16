use std::cmp;
use time::Date;

use crate::duration::Duration;

/// # DateRange
///
/// Simply comprises a pair of [`time::Date`] objects that represent
/// the start and end of a date range
///
/// Range works liks standard Rust ranges: the lower bound is inclusive
/// and the upper bound is exclusive. Therefore, the month of June would
/// be represented as 1-Jun to 1-Jul
///
/// Can be converted into a `Duration` object, or created from a `Duration`
/// plus a `Date`. This allows for both assessing a date_diff and a date_add
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DateRange {
    pub(crate) from: Date,
    pub(crate) to: Date,
}

impl DateRange {
    // region: constructors
    /// Creates a new `DateRange` object.
    /// Reorders the arguments to ensure the from part is always the start of the
    /// timeline, i.e. the earliest date
    pub fn new(from: Date, to: Date) -> Self {
        if from < to {
            Self { from, to }
        } else {
            Self { to, from }
        }
    }

    /// Creates a new `DateRange` object from a `Date` and a
    /// `Duration`
    pub fn from_duration(from: Date, dur: Duration) -> Self {
        let to = from + dur;
        Self::new(from, to.primary())
    }
    // endregion constructors

    // region: getters
    pub fn from(&self) -> Date {
        self.from
    }

    pub fn to(&self) -> Date {
        self.to
    }
    // endregion getters

    // region: conversion
    /// Return a `Duration` that represents the `DateRange` time span
    pub fn as_duration(&self) -> Duration {
        Duration::from_dates(self.from, self.to)
    }

    /// Return the number of days in the `DateRange`
    pub fn as_days(&self) -> i32 {
        self.to.to_julian_day() - self.from.to_julian_day()
    }

    /// Return the number of weeks that can fit in the `DateRange`.
    /// If inc_part is false, part weeks will be discarded e.g. 13 days -> 1 week.
    /// If inc_part is true, part weeks will count as an extra period e.g. 13 days -> 2 weeks.
    pub fn as_weeks(&self, inc_part: bool) -> i32 {
        self.as_days() / 7
            + if inc_part && (self.as_days() % 7 > 0) {
                1
            } else {
                0
            }
    }

    /// Return the number of months that can fit in the `DateRange`.
    /// If inc_part is false, part months will be discarded e.g. 45 days -> 1 month.
    /// If inc_part is true, part months will count as an extra period e.g. 45 days -> 2 months.
    pub fn as_months(&self, inc_part: bool) -> i32 {
        let dur = self.as_duration();
        dur.years() * 12 + dur.months() + if inc_part && (dur.days() > 0) { 1 } else { 0 }
    }

    /// Return the number of quarters that can fit in the `DateRange`.
    /// If inc_part is false, part quarters will be discarded e.g. 145 days -> 1 quarter.
    /// If inc_part is true, part quarters will count as an extra period e.g. 145 days -> 2 quarters.
    pub fn as_quarters(&self, inc_part: bool) -> i32 {
        self.as_months(inc_part) / 3
            + if inc_part && (self.as_months(inc_part) % 3 > 0) {
                1
            } else {
                0
            }
    }

    /// Return the number of years that can fit in the `DateRange`.
    /// If inc_part is false, part years will be discarded e.g. 500 days -> 1 year.
    /// If inc_part is true, part years will count as an extra period e.g. 500 days -> 2 years.
    pub fn as_years(&self, inc_part: bool) -> i32 {
        let dur = self.as_duration();
        dur.years()
            + if inc_part && (dur.days() > 0 || dur.months() > 0) {
                1
            } else {
                0
            }
    }
    // endregion conversion

    // region: utility
    /// Returns a `DateRange` that represents the intersection
    /// of the two input `DateRange`. Is an Option to allow for
    /// the the two ranges not overlapping, in which case None is returned
    pub fn intersect(&self, other: &DateRange) -> Option<DateRange> {
        if other.from > self.to || other.to < self.from {
            None
        } else {
            let from = cmp::max(self.from, other.from);
            let to = cmp::max(self.to, other.to);
            Some(DateRange::new(from, to))
        }
    }

    // TODO: consider whether this should be an Option, with None being
    // returned where the two DateRanges are disjoint
    /// Returns the union of the two input `DateRange`. Since
    /// `DateRange` cannot be disjoint, this will span from the
    /// earliest start date to the latest end date, with no regard
    /// for whether the porition in between is continuous
    pub fn union(&self, other: &DateRange) -> DateRange {
        let from = cmp::min(self.from, other.from);
        let to = cmp::max(self.to, other.to);
        DateRange::new(from, to)
    }

    /// Does the `DateRange` contain the `Date`?
    pub fn contains(&self, date: Date) -> bool {
        self.from <= date && self.to > date
    }
    // endregion utility
}

#[cfg(test)]
mod tests {

    use super::*;
    use time::Month;

    #[test]
    fn create_daterange() {
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let d2 = Date::from_calendar_date(2022, Month::June, 15).unwrap();
        let dr = DateRange::new(d1, d2);
        assert_eq!(dr.from().day(), 15);
    }

    #[test]
    fn period_length() {}

    #[test]
    fn period_iterator() {}

    // TODO: write some proper tests!
}
