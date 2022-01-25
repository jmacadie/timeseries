use time::{Date, Month, util::days_in_year_month};
use crate::{Period, DateRange};
use std::cmp;

/// # Timeline
/// 
/// An object that represnts a contiguous period of time and an assocaited
/// periodicity. The periodicity defines the chunks of time the timeline will be
/// apportioned into and currently implements:
/// * Daily
/// * Weekly
/// * Monthly
/// * Quarterly
/// * Annual
/// 
/// Because the time range is not guaranteed to be a whole number of time periods,
/// the final period can be a short period. For example, a timeline that is 3 months
/// and 2 days, with periodicity of monthly will comprise 4 time periods. The first
/// three periods will be whole months and the final one will be 2 days
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TimeLine {
    pub(crate)range: DateRange,
    periodicity: Period,
    current_date: Date,
    pub(crate) len: i32,
}

impl TimeLine {
    
    pub fn new(range: DateRange, periodicity: Period) -> Self {
        let curr = range.from().clone();
        let len = TimeLine::range_len(range, periodicity);
        TimeLine {
            range,
            periodicity,
            current_date: curr,
            len,
        }
    }

    // TODO: don't take a range but dates from and to. This should support the new function that can index at a date
    /// Returns the number of time periods that will occur over the date
    /// range for a given periodicity.
    /// 
    /// Note that a fractional period at the end will be counted as a whole period
    /// e.g. if the time period is two months and a day and the periodicity is 
    /// monthly then there will be 3 periods, the final one being only one
    /// day long.
    fn range_len(range: DateRange, periodicity: Period) -> i32 {
        let mut diff: i32;
        match periodicity {
            Period::Day => {
                range.to.to_julian_day() - range.from.to_julian_day()
            },
            Period::Week => {
                (range.to.to_julian_day() - range.from.to_julian_day()) / 7
            },
            Period::Month => {
                diff = 12 * (range.to.year() - range.from.year());
                // get the ordinal value of the  month out of the Month enum
                let m1 = range.to.month() as i32; 
                let m2 = range.from.month() as i32;
                diff += m1 - m2;
                if (m1 == m2) && (range.to.day() > range.from.day()) { diff += 1; }
                diff
            },
            Period::Quarter => {
                diff = 4 * (range.to.year() - range.from.year());
                // get the ordinal value of the  month out of the Month enum
                let m1 = range.to.month() as i32; 
                let m2 = range.from.month() as i32;
                diff += (m1 - m2) / 4;
                if (m1 == m2) && (range.to.day() > range.from.day()) { diff += 1; }
                diff
            },
            Period::Year => {
                diff = range.to.year() - range.from.year();
                // get the ordinal value of the  month out of the Month enum
                let m1 = range.to.month() as i8;
                let m2 = range.from.month() as i8;
                if m1 > m2 { diff += 1; }
                if (m1 == m2) && (range.to.day() > range.from.day()) { diff += 1; }
                diff
            },
        }
    }

    // TODO: write the following:
    //  * a function to return the index at a given date. Will be needed by the TimeSeries object to extract values at a given date
    //  * a function to change periodicity. For example can see wanting to summarise up from Monthly calcs to an annual output
    //  * a getter for an individual time period, returned as a DateRange
    //  * a getter for a time slice (maybe? need to think of the use case)
    
    // TODO: even needed?
    pub fn merge(self, other: TimeLine) -> Result<Option<TimeLine>, &'static str> {
        if self == other { return Ok(None); }
        if self.periodicity != other.periodicity { return Err("Time periods do match"); }
        Ok(
            Some(
                TimeLine::new(self.range.union(&other.range), self.periodicity.clone())
            )
        )
    }

}

impl Iterator for TimeLine {
    type Item = DateRange;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current_date == *self.range.to() { return None; }

        let mut next_date = self.current_date.clone();
        match self.periodicity {
            Period::Day => {
                next_date = match next_date.next_day() {
                    Some(d) => d,
                    None => { return None; },
                }
            },
            Period::Week => {
                for _ in 1..8 {
                    next_date = match next_date.next_day() {
                        Some(d) => d,
                        None => { return None; },
                    }
                }
            },
            Period::Month => {
                let (mut y, mut m, mut d) = next_date.to_calendar_date();
                m = m.next();
                if m == Month::January { y += 1 };
                d = cmp::min(days_in_year_month(y, m), d);
                next_date = match Date::from_calendar_date(y, m, d) {
                    Ok(d) => d,
                    Err(_) => { return None; },
                }
            },
            Period::Quarter => {
                let (mut y, mut m, mut d) = next_date.to_calendar_date();
                for _ in 1..4 {
                    m = m.next();
                    if m == Month::January { y += 1 };
                }
                d = cmp::min(days_in_year_month(y, m), d);
                next_date = match Date::from_calendar_date(y, m, d) {
                    Ok(d) => d,
                    Err(_) => { return None; },
                }
            },
            Period::Year => {
                let (y, m, d) = next_date.to_calendar_date();
                next_date = match Date::from_calendar_date(y + 1, m, d) {
                    Ok(d) => d,
                    Err(_) => { return None; },
                }
            },
        }
        
        if next_date > *self.range.to() { next_date = self.range.to().clone(); } 

        let date_range = DateRange::new(self.current_date, next_date);
        self.current_date = date_range.to().clone();
        Some(date_range)
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn create_timeline() {}

    #[test]
    fn period_length() {}

    #[test]
    fn period_iterator() {}
    
    // TODO: write some proper tests!

    #[test]
    fn from_test() {
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2022, Month::December, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = TimeLine::new(dr, Period::Quarter);
        let mut i = 0;
        for test_range in tl {
            assert_eq!(test_range.to().year(), 2022);
            i += 1;
            if i > 4 { break; }
        }
    }
}