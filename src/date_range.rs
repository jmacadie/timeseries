use std::cmp;
use time::Date;

use crate::{Duration, TimeSeriesError};

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
            Self { from: to, to: from }
        }
    }

    /// Creates a new `DateRange` object from a `Date` and a
    /// `Duration`
    pub fn from_duration(from: Date, dur: Duration) -> Result<Self, TimeSeriesError> {
        let to = (from + dur)?;
        Ok(Self::new(from, to.primary()))
    }
    // endregion constructors

    // region: getters
    pub fn from(&self) -> Date {
        self.from
    }

    pub fn to(&self) -> Date {
        self.to
    }

    /// Retun last valid day inside the `DateRange`, as by
    /// definition `to` is just outside the `DateRange`
    pub fn last_day(&self) -> Date {
        self.to.previous_day().unwrap_or(self.to)
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
        if other.from >= self.to || other.to <= self.from {
            None
        } else {
            let from = cmp::max(self.from, other.from);
            let to = cmp::min(self.to, other.to);
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

    /// Tests if the source date range contains the whole of the
    /// second date range
    pub fn fully_contains(&self, other: &DateRange) -> bool {
        self.from <= other.from && self.to >= other.to
    }

    // endregion utility
}

#[cfg(test)]
mod tests {

    use super::*;
    use time::Month;

    #[test]
    fn create_daterange() {
        // Create the normal way round
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let d2 = Date::from_calendar_date(2022, Month::June, 15).unwrap();
        let mut dr = DateRange::new(d1, d2);
        assert_eq!(
            (dr.from().day(), dr.from().month(), dr.from().year()),
            (15, Month::January, 2022),
            "Normal way round - from",
        );
        assert_eq!(
            (dr.to().day(), dr.to().month(), dr.to().year()),
            (15, Month::June, 2022),
            "Normal way round - to",
        );

        // Create with dates reversed
        dr = DateRange::new(d2, d1);
        assert_eq!(
            (dr.from().day(), dr.from().month(), dr.from().year()),
            (15, Month::January, 2022),
            "Reversed dates - from",
        );
        assert_eq!(
            (dr.to().day(), dr.to().month(), dr.to().year()),
            (15, Month::June, 2022),
            "Reversed dates - to",
        );
    }

    #[test]
    fn create_from_duration() {
        // Try 1 day
        let d = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let mut dur = Duration::new(1, 0, 0);
        let mut dr = DateRange::from_duration(d, dur).unwrap();
        assert_eq!(
            (dr.from().day(), dr.from().month(), dr.from().year()),
            (15, Month::January, 2022)
        );
        assert_eq!(
            (dr.to().day(), dr.to().month(), dr.to().year()),
            (16, Month::January, 2022)
        );

        // Try 100 days
        dur = Duration::new(100, 0, 0);
        dr = DateRange::from_duration(d, dur).unwrap();
        assert_eq!(
            (dr.from().day(), dr.from().month(), dr.from().year()),
            (15, Month::January, 2022)
        );
        assert_eq!(
            (dr.to().day(), dr.to().month(), dr.to().year()),
            (25, Month::April, 2022)
        );

        // Try 1 month
        dur = Duration::new(0, 1, 0);
        dr = DateRange::from_duration(d, dur).unwrap();
        assert_eq!(
            (dr.from().day(), dr.from().month(), dr.from().year()),
            (15, Month::January, 2022)
        );
        assert_eq!(
            (dr.to().day(), dr.to().month(), dr.to().year()),
            (15, Month::February, 2022)
        );

        // Try 15 months
        dur = Duration::new(0, 15, 0);
        dr = DateRange::from_duration(d, dur).unwrap();
        assert_eq!(
            (dr.from().day(), dr.from().month(), dr.from().year()),
            (15, Month::January, 2022)
        );
        assert_eq!(
            (dr.to().day(), dr.to().month(), dr.to().year()),
            (15, Month::April, 2023)
        );

        // Try 1 year
        dur = Duration::new(0, 0, 1);
        dr = DateRange::from_duration(d, dur).unwrap();
        assert_eq!(
            (dr.from().day(), dr.from().month(), dr.from().year()),
            (15, Month::January, 2022)
        );
        assert_eq!(
            (dr.to().day(), dr.to().month(), dr.to().year()),
            (15, Month::January, 2023)
        );
    }

    #[test]
    fn last_day() {
        // Test a normal date
        let d1 = Date::from_calendar_date(2020, Month::January, 15).unwrap();
        let mut d2 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let mut dr = DateRange::new(d1, d2);
        assert_eq!(
            (
                dr.last_day().day(),
                dr.last_day().month(),
                dr.last_day().year()
            ),
            (14, Month::January, 2022)
        );

        // Test end of month - long
        d2 = Date::from_calendar_date(2022, Month::November, 1).unwrap();
        dr = DateRange::new(d1, d2);
        assert_eq!(
            (
                dr.last_day().day(),
                dr.last_day().month(),
                dr.last_day().year()
            ),
            (31, Month::October, 2022)
        );

        // Test end of month - short
        d2 = Date::from_calendar_date(2022, Month::May, 1).unwrap();
        dr = DateRange::new(d1, d2);
        assert_eq!(
            (
                dr.last_day().day(),
                dr.last_day().month(),
                dr.last_day().year()
            ),
            (30, Month::April, 2022)
        );

        // Test end of year
        d2 = Date::from_calendar_date(2022, Month::January, 1).unwrap();
        dr = DateRange::new(d1, d2);
        assert_eq!(
            (
                dr.last_day().day(),
                dr.last_day().month(),
                dr.last_day().year()
            ),
            (31, Month::December, 2021)
        );
    }

    #[test]
    fn as_duration() {
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let mut d2 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let mut dr = DateRange::new(d1, d2);
        let mut dur = dr.as_duration();
        assert_eq!((dur.days(), dur.months(), dur.years()), (0, 0, 0));

        d2 = Date::from_calendar_date(2022, Month::January, 20).unwrap();
        dr = DateRange::new(d1, d2);
        dur = dr.as_duration();
        assert_eq!((dur.days(), dur.months(), dur.years()), (5, 0, 0));

        d2 = Date::from_calendar_date(2022, Month::June, 15).unwrap();
        dr = DateRange::new(d1, d2);
        dur = dr.as_duration();
        assert_eq!((dur.days(), dur.months(), dur.years()), (0, 5, 0));

        d2 = Date::from_calendar_date(2024, Month::January, 15).unwrap();
        dr = DateRange::new(d1, d2);
        dur = dr.as_duration();
        assert_eq!((dur.days(), dur.months(), dur.years()), (0, 0, 2));

        d2 = Date::from_calendar_date(2024, Month::August, 12).unwrap();
        dr = DateRange::new(d1, d2);
        dur = dr.as_duration();
        assert_eq!((dur.days(), dur.months(), dur.years()), (28, 6, 2));
    }

    #[test]
    fn as_days() {
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let mut d2 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let mut dr = DateRange::new(d1, d2);
        let mut i = dr.as_days();
        assert_eq!(i, 0);

        d2 = Date::from_calendar_date(2024, Month::April, 30).unwrap();
        dr = DateRange::new(d1, d2);
        i = dr.as_days();
        assert_eq!(i, 836);
    }

    #[test]
    fn as_weeks() {
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let mut d2 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let mut dr = DateRange::new(d1, d2);
        let mut i = dr.as_weeks(true);
        assert_eq!(i, 0);

        d2 = Date::from_calendar_date(2024, Month::April, 30).unwrap();
        dr = DateRange::new(d1, d2);
        i = dr.as_weeks(false);
        assert_eq!(i, 119);
        i = dr.as_weeks(true);
        assert_eq!(i, 120);
    }

    #[test]
    fn as_months() {
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let mut d2 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let mut dr = DateRange::new(d1, d2);
        let mut i = dr.as_months(true);
        assert_eq!(i, 0);

        d2 = Date::from_calendar_date(2024, Month::April, 30).unwrap();
        dr = DateRange::new(d1, d2);
        i = dr.as_months(false);
        assert_eq!(i, 27);
        i = dr.as_months(true);
        assert_eq!(i, 28);
    }

    #[test]
    fn as_quarters() {
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let mut d2 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let mut dr = DateRange::new(d1, d2);
        let mut i = dr.as_quarters(true);
        assert_eq!(i, 0);

        d2 = Date::from_calendar_date(2024, Month::April, 30).unwrap();
        dr = DateRange::new(d1, d2);
        i = dr.as_quarters(false);
        assert_eq!(i, 9);
        i = dr.as_quarters(true);
        assert_eq!(i, 10);
    }

    #[test]
    fn as_years() {
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let mut d2 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let mut dr = DateRange::new(d1, d2);
        let mut i = dr.as_years(true);
        assert_eq!(i, 0);

        d2 = Date::from_calendar_date(2024, Month::April, 30).unwrap();
        dr = DateRange::new(d1, d2);
        i = dr.as_years(false);
        assert_eq!(i, 2);
        i = dr.as_years(true);
        assert_eq!(i, 3);
    }

    #[test]
    fn intersect() {
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let d2 = Date::from_calendar_date(2023, Month::January, 15).unwrap();
        let dr1 = DateRange::new(d1, d2);

        // Disjoint - returns None
        let mut d3 = Date::from_calendar_date(2020, Month::January, 15).unwrap();
        let mut d4 = Date::from_calendar_date(2021, Month::January, 15).unwrap();
        let mut dr2 = DateRange::new(d3, d4);
        assert_eq!(dr1.intersect(&dr2), None);

        // Touching - returns None
        d3 = Date::from_calendar_date(2020, Month::January, 15).unwrap();
        d4 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        dr2 = DateRange::new(d3, d4);
        assert_eq!(dr1.intersect(&dr2), None);

        // Overlap one side
        d3 = Date::from_calendar_date(2020, Month::January, 15).unwrap();
        d4 = Date::from_calendar_date(2022, Month::March, 15).unwrap();
        dr2 = DateRange::new(d3, d4);
        let mut dr_out = DateRange::new(d1, d4);
        assert_eq!(dr1.intersect(&dr2), Some(dr_out));

        // Range within start range
        d3 = Date::from_calendar_date(2022, Month::January, 31).unwrap();
        d4 = Date::from_calendar_date(2022, Month::March, 15).unwrap();
        dr2 = DateRange::new(d3, d4);
        dr_out = DateRange::new(d3, d4);
        assert_eq!(dr1.intersect(&dr2), Some(dr_out));

        // Range without start range
        d3 = Date::from_calendar_date(2020, Month::January, 15).unwrap();
        d4 = Date::from_calendar_date(2032, Month::March, 15).unwrap();
        dr2 = DateRange::new(d3, d4);
        dr_out = DateRange::new(d1, d2);
        assert_eq!(dr1.intersect(&dr2), Some(dr_out));
    }

    #[test]
    fn union() {
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let d2 = Date::from_calendar_date(2023, Month::January, 15).unwrap();
        let dr1 = DateRange::new(d1, d2);

        // Disjoint
        let mut d3 = Date::from_calendar_date(2020, Month::January, 15).unwrap();
        let mut d4 = Date::from_calendar_date(2021, Month::January, 15).unwrap();
        let mut dr2 = DateRange::new(d3, d4);
        let mut dr_out = DateRange::new(d3, d2);
        assert_eq!(dr1.union(&dr2), dr_out, "Disjoint");

        // Overlap one side
        d3 = Date::from_calendar_date(2020, Month::January, 15).unwrap();
        d4 = Date::from_calendar_date(2022, Month::March, 15).unwrap();
        dr2 = DateRange::new(d3, d4);
        dr_out = DateRange::new(d3, d2);
        assert_eq!(dr1.union(&dr2), dr_out, "Overlap one side");

        // Range within start range
        d3 = Date::from_calendar_date(2022, Month::January, 31).unwrap();
        d4 = Date::from_calendar_date(2022, Month::March, 15).unwrap();
        dr2 = DateRange::new(d3, d4);
        dr_out = DateRange::new(d1, d2);
        assert_eq!(dr1.union(&dr2), dr_out, "Within");

        // Range without start range
        d3 = Date::from_calendar_date(2020, Month::January, 15).unwrap();
        d4 = Date::from_calendar_date(2032, Month::March, 15).unwrap();
        dr2 = DateRange::new(d3, d4);
        dr_out = DateRange::new(d3, d4);
        assert_eq!(dr1.union(&dr2), dr_out, "Without");
    }

    #[test]
    fn contains() {
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let d2 = Date::from_calendar_date(2023, Month::January, 15).unwrap();
        let dr = DateRange::new(d1, d2);

        // Date before
        let mut d3 = Date::from_calendar_date(2020, Month::January, 15).unwrap();
        assert!(!dr.contains(d3));

        // Start date
        assert!(dr.contains(d1));

        // Date within
        d3 = Date::from_calendar_date(2022, Month::June, 15).unwrap();
        assert!(dr.contains(d3));

        // End date
        assert!(!dr.contains(d2));

        // Date after
        d3 = Date::from_calendar_date(2027, Month::January, 15).unwrap();
        assert!(!dr.contains(d3));
    }

    #[test]
    fn fully_contains() {
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let d2 = Date::from_calendar_date(2023, Month::January, 15).unwrap();
        let dr = DateRange::new(d1, d2);

        // Same Date Range
        let mut d3 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let mut d4 = Date::from_calendar_date(2023, Month::January, 15).unwrap();
        let mut dr2 = DateRange::new(d3, d4);
        assert!(dr.fully_contains(&dr2));

        // Date Range within
        d3 = Date::from_calendar_date(2022, Month::February, 1).unwrap();
        d4 = Date::from_calendar_date(2022, Month::December, 31).unwrap();
        dr2 = DateRange::new(d3, d4);
        assert!(dr.fully_contains(&dr2));

        // Date Range earlier
        d3 = Date::from_calendar_date(2022, Month::January, 14).unwrap();
        d4 = Date::from_calendar_date(2022, Month::December, 31).unwrap();
        dr2 = DateRange::new(d3, d4);
        assert!(!dr.fully_contains(&dr2));

        // Date Range later
        d3 = Date::from_calendar_date(2022, Month::February, 1).unwrap();
        d4 = Date::from_calendar_date(2023, Month::January, 16).unwrap();
        dr2 = DateRange::new(d3, d4);
        assert!(!dr.fully_contains(&dr2));
    }
}
