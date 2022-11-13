use crate::{DateRange, Duration, Period};
use std::cmp;
use time::{util::days_in_year_month, Date, Month};

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
pub struct Timeline {
    pub(crate) range: DateRange,
    pub(crate) periodicity: Period,
    pub(crate) len: usize,
}

#[allow(clippy::len_without_is_empty)]
impl Timeline {
    // region: constructors
    /// Create a new Timeline
    #[must_use]
    pub fn new(range: DateRange, periodicity: Period) -> Self {
        let len = match periodicity {
            Period::Day => Self::get_len(range.as_days()),
            Period::Week => Self::get_len(range.as_weeks(true)),
            Period::Month => Self::get_len(range.as_months(true)),
            Period::Quarter => Self::get_len(range.as_quarters(true)),
            Period::Year => Self::get_len(range.as_years(true)),
        };
        Timeline {
            range,
            periodicity,
            len,
        }
    }

    /// Internal function do deal with the faff og casting from
    /// i32 to usize. Run an abs on the range and then coerce any
    /// errors to zero
    fn get_len(range: i32) -> usize {
        let abs = range.checked_abs().unwrap_or(0);
        usize::try_from(abs).unwrap_or(0)
    }

    /// Create a new timeline with the same start and end dates
    /// but with different periodicity
    #[must_use]
    pub fn change_periodicity(&self, new: Period) -> Self {
        Timeline::new(self.range, new)
    }
    // endregion constructors

    // region: getters
    /// Return the Date Range of the Timeline
    #[must_use]
    pub fn range(&self) -> DateRange {
        self.range
    }

    /// Return the periodicity of the Timeline
    #[must_use]
    pub fn periodicity(&self) -> Period {
        self.periodicity
    }

    /// Return the length of the Timeline
    #[must_use]
    pub fn len(&self) -> usize {
        self.len
    }
    // endregion getters

    // region: indexing
    /// Return the index position of the date within the
    /// timeline. Returns None if the date is outside of
    /// the timeline
    #[must_use]
    pub fn index_at(&self, date: Date) -> Option<usize> {
        if !self.range.contains(date) {
            return None;
        }
        let tmp_range = DateRange::new(self.range.from, date);
        match self.periodicity {
            Period::Day => Some(Self::get_len(tmp_range.as_days())),
            Period::Week => Some(Self::get_len(tmp_range.as_weeks(false))),
            Period::Month => Some(Self::get_len(tmp_range.as_months(false))),
            Period::Quarter => Some(Self::get_len(tmp_range.as_quarters(false))),
            Period::Year => Some(Self::get_len(tmp_range.as_years(false))),
        }
    }

    /// Return the date range that represents a single period at the index.
    /// Period is defined by the periodicity of the Timeline,
    /// so a monthly timeline would return a month date range
    #[must_use]
    pub fn index(&self, mut idx: i32) -> Option<DateRange> {
        let len = i32::try_from(self.len).ok()?;
        if idx >= len || idx < -len {
            return None;
        }
        if idx < 0 {
            idx += len;
        }
        let dur1: Duration;
        let dur2: Duration;
        match self.periodicity {
            Period::Day => {
                dur1 = Duration::new(idx, 0, 0);
                dur2 = Duration::new(1, 0, 0);
            }
            Period::Week => {
                dur1 = Duration::new(7 * idx, 0, 0);
                dur2 = Duration::new(7, 0, 0);
            }
            Period::Month => {
                dur1 = Duration::new(0, idx, 0);
                dur2 = Duration::new(0, 1, 0);
            }
            Period::Quarter => {
                dur1 = Duration::new(0, 3 * idx, 0);
                dur2 = Duration::new(0, 3, 0);
            }
            Period::Year => {
                dur1 = Duration::new(0, 0, idx);
                dur2 = Duration::new(0, 0, 1);
            }
        };
        let start = (self.range.from + dur1).ok()?.primary();
        let mut end = (start + dur2).ok()?.primary();
        end = cmp::min(end, self.range.to);
        Some(DateRange::new(start, end))
    }
    // endregion indexing

    // region: head_tail
    #[must_use]
    pub fn head(&self) -> Option<DateRange> {
        self.index(0)
    }

    #[must_use]
    pub fn tail(&self) -> Option<Timeline> {
        let head = self.head()?;
        let tail_range = DateRange::new(head.to, self.range.to());
        Some(Timeline::new(tail_range, self.periodicity))
    }

    #[must_use]
    pub fn split_first(&self) -> (Option<DateRange>, Option<Timeline>) {
        (self.head(), self.tail())
    }
    // endregion head_tail
    // TODO: Head, tail, split...
}

// region: iterators
// Not going to implement the owned iterator since `Timeline` is `Copy`
// No point implementing mut ref iterator as the underlying dateranges don't exist

// region: ref_iterator
pub struct Iter {
    range: DateRange,
    periodicity: Period,
    current_date: Date,
}

impl Iterator for Iter {
    type Item = DateRange;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current_date == self.range.to() {
            return None;
        }

        let mut next_date = self.current_date;
        match self.periodicity {
            Period::Day => {
                next_date = next_date.next_day()?;
            }
            Period::Week => {
                for _ in 0..7 {
                    next_date = next_date.next_day()?;
                }
            }
            Period::Month => {
                let (mut y, mut m, mut d) = next_date.to_calendar_date();
                m = m.next();
                if m == Month::January {
                    y += 1;
                };
                d = cmp::min(days_in_year_month(y, m), d);
                next_date = Date::from_calendar_date(y, m, d).ok()?;
            }
            Period::Quarter => {
                let (mut y, mut m, mut d) = next_date.to_calendar_date();
                for _ in 0..3 {
                    m = m.next();
                    if m == Month::January {
                        y += 1;
                    };
                }
                d = cmp::min(days_in_year_month(y, m), d);
                next_date = Date::from_calendar_date(y, m, d).ok()?;
            }
            Period::Year => {
                let (y, m, d) = next_date.to_calendar_date();
                next_date = Date::from_calendar_date(y + 1, m, d).ok()?;
            }
        }

        if next_date > self.range.to() {
            next_date = self.range.to();
        }

        let date_range = DateRange::new(self.current_date, next_date);
        self.current_date = date_range.to();
        Some(date_range)
    }
}

impl Timeline {
    fn iter(&self) -> Iter {
        Iter {
            range: self.range,
            periodicity: self.periodicity,
            current_date: self.range.from,
        }
    }
}

impl IntoIterator for &Timeline {
    type Item = DateRange;
    type IntoIter = Iter;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
// endregion ref_iterator
// endregion iterators

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn create_timeline() {
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let d2 = Date::from_calendar_date(2024, Month::June, 15).unwrap();
        let dr = DateRange::new(d1, d2);

        let mut tl = Timeline::new(dr, Period::Day);
        assert_eq!(tl.len, 882);
        tl = Timeline::new(dr, Period::Week);
        assert_eq!(tl.len, 126);
        tl = Timeline::new(dr, Period::Month);
        assert_eq!(tl.len, 29);
        tl = Timeline::new(dr, Period::Quarter);
        assert_eq!(tl.len, 10);
        tl = Timeline::new(dr, Period::Year);
        assert_eq!(tl.len, 3);
    }

    #[test]
    fn change_periodicity() {
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let d2 = Date::from_calendar_date(2024, Month::June, 15).unwrap();
        let dr = DateRange::new(d1, d2);
        let tl = Timeline::new(dr, Period::Day);

        let mut tl2 = tl.change_periodicity(Period::Week);
        assert_eq!(tl2.len, 126);
        tl2 = tl.change_periodicity(Period::Month);
        assert_eq!(tl2.len, 29);
        tl2 = tl.change_periodicity(Period::Quarter);
        assert_eq!(tl2.len, 10);
        tl2 = tl.change_periodicity(Period::Year);
        assert_eq!(tl2.len, 3);
    }

    #[test]
    fn range() {
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let d2 = Date::from_calendar_date(2024, Month::June, 15).unwrap();
        let dr = DateRange::new(d1, d2);
        let tl = Timeline::new(dr, Period::Day);

        let from = tl.range().from;
        let to = tl.range().to;
        assert_eq!(from, d1);
        assert_eq!(to, d2);
    }

    #[test]
    fn periodicity() {
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let d2 = Date::from_calendar_date(2024, Month::June, 15).unwrap();
        let dr = DateRange::new(d1, d2);
        let tl = Timeline::new(dr, Period::Day);

        assert_eq!(tl.periodicity(), Period::Day);
    }

    #[test]
    fn index_at() {
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let d2 = Date::from_calendar_date(2024, Month::June, 15).unwrap();
        let d3 = Date::from_calendar_date(2023, Month::August, 17).unwrap();
        let dr = DateRange::new(d1, d2);
        let tl = Timeline::new(dr, Period::Day);

        // Test in bounds with each of the Periodicities
        assert_eq!(tl.index_at(d3), Some(579));
        assert_eq!(tl.change_periodicity(Period::Week).index_at(d3), Some(82));
        assert_eq!(tl.change_periodicity(Period::Month).index_at(d3), Some(19));
        assert_eq!(tl.change_periodicity(Period::Quarter).index_at(d3), Some(6));
        assert_eq!(tl.change_periodicity(Period::Year).index_at(d3), Some(1));

        // Test out of bounds for None
        let mut d4 = Date::from_calendar_date(2021, Month::August, 17).unwrap();
        assert_eq!(tl.index_at(d4), None);
        d4 = Date::from_calendar_date(2028, Month::August, 17).unwrap();
        assert_eq!(tl.index_at(d4), None);
    }

    #[test]
    fn index() {
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let d2 = Date::from_calendar_date(2024, Month::June, 15).unwrap();
        let dr = DateRange::new(d1, d2);
        let tl = Timeline::new(dr, Period::Day);

        let mut dtmep1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let mut dtmep2 = Date::from_calendar_date(2022, Month::January, 16).unwrap();
        let mut drtemp = DateRange::new(dtmep1, dtmep2);
        assert_eq!(tl.index(0), Some(drtemp), "Check first day");

        dtmep1 = Date::from_calendar_date(2023, Month::August, 17).unwrap();
        dtmep2 = Date::from_calendar_date(2023, Month::August, 18).unwrap();
        drtemp = DateRange::new(dtmep1, dtmep2);
        assert_eq!(tl.index(579), Some(drtemp), "Check day");

        dtmep1 = Date::from_calendar_date(2023, Month::August, 12).unwrap();
        dtmep2 = Date::from_calendar_date(2023, Month::August, 19).unwrap();
        drtemp = DateRange::new(dtmep1, dtmep2);
        assert_eq!(
            tl.change_periodicity(Period::Week).index(82),
            Some(drtemp),
            "Check week"
        );

        dtmep1 = Date::from_calendar_date(2023, Month::August, 15).unwrap();
        dtmep2 = Date::from_calendar_date(2023, Month::September, 15).unwrap();
        drtemp = DateRange::new(dtmep1, dtmep2);
        assert_eq!(
            tl.change_periodicity(Period::Month).index(19),
            Some(drtemp),
            "Check Month"
        );

        dtmep1 = Date::from_calendar_date(2023, Month::July, 15).unwrap();
        dtmep2 = Date::from_calendar_date(2023, Month::October, 15).unwrap();
        drtemp = DateRange::new(dtmep1, dtmep2);
        assert_eq!(
            tl.change_periodicity(Period::Quarter).index(6),
            Some(drtemp),
            "Check Quarter"
        );

        dtmep1 = Date::from_calendar_date(2023, Month::January, 15).unwrap();
        dtmep2 = Date::from_calendar_date(2024, Month::January, 15).unwrap();
        drtemp = DateRange::new(dtmep1, dtmep2);
        assert_eq!(
            tl.change_periodicity(Period::Year).index(1),
            Some(drtemp),
            "Check Year"
        );

        // Check out of bounds
        assert_eq!(tl.index(882), None);
        assert_eq!(tl.index(-883), None);

        // Check negative indexes in from end
        dtmep1 = Date::from_calendar_date(2024, Month::June, 14).unwrap();
        dtmep2 = Date::from_calendar_date(2024, Month::June, 15).unwrap();
        drtemp = DateRange::new(dtmep1, dtmep2);
        assert_eq!(
            tl.index(-1),
            Some(drtemp),
            "Check last day with negative index"
        );

        dtmep1 = Date::from_calendar_date(2023, Month::November, 28).unwrap();
        dtmep2 = Date::from_calendar_date(2023, Month::November, 29).unwrap();
        drtemp = DateRange::new(dtmep1, dtmep2);
        assert_eq!(
            tl.index(-200),
            Some(drtemp),
            "Check other day with negative index"
        );
    }

    #[test]
    fn period_iterator() {
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let d2 = Date::from_calendar_date(2024, Month::June, 19).unwrap();
        let dr = DateRange::new(d1, d2);

        // Iterate Days
        let mut tl = Timeline::new(dr, Period::Day);
        let mut counter = 0;
        for dr in &tl {
            if counter == 0 {
                assert_eq!(dr, tl.index(0).unwrap(), "First Day");
            }
            counter += 1;
            if counter == 886 {
                assert_eq!(dr, tl.index(-1).unwrap(), "Last Day");
            }
        }
        assert_eq!(counter, 886, "Iterated right number of days");

        // Iterate Weeks
        tl = tl.change_periodicity(Period::Week);
        counter = 0;
        for dr in &tl {
            if counter == 0 {
                assert_eq!(dr, tl.index(0).unwrap(), "First Week");
            }
            counter += 1;
            if counter == 127 {
                assert_eq!(dr, tl.index(-1).unwrap(), "Last Week");
            }
        }
        assert_eq!(counter, 127, "Iterated right number of weeks");

        // Iterate Months
        tl = tl.change_periodicity(Period::Month);
        counter = 0;
        for dr in &tl {
            if counter == 0 {
                assert_eq!(dr, tl.index(0).unwrap(), "First Month");
            }
            counter += 1;
            if counter == 30 {
                assert_eq!(dr, tl.index(-1).unwrap(), "Last Month");
            }
        }
        assert_eq!(counter, 30, "Iterated right number of months");

        // Iterate Quarters
        tl = tl.change_periodicity(Period::Quarter);
        counter = 0;
        for dr in &tl {
            if counter == 0 {
                assert_eq!(dr, tl.index(0).unwrap(), "First Quarter");
            }
            counter += 1;
            if counter == 10 {
                assert_eq!(dr, tl.index(-1).unwrap(), "Last Quarter");
            }
        }
        assert_eq!(counter, 10, "Iterated right number of quarters");

        // Iterate Years
        tl = tl.change_periodicity(Period::Year);
        counter = 0;
        for dr in &tl {
            if counter == 0 {
                assert_eq!(dr, tl.index(0).unwrap(), "First Year");
            }
            counter += 1;
            if counter == 3 {
                assert_eq!(dr, tl.index(-1).unwrap(), "Last Year");
            }
        }
        assert_eq!(counter, 3, "Iterated right number of years");
    }

    #[test]
    fn from_test() {
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2022, Month::December, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = Timeline::new(dr, Period::Quarter);
        let mut i = 0;
        for test_range in &tl {
            assert_eq!(test_range.to().year(), 2022);
            i += 1;
            if i > 4 {
                break;
            }
        }
    }
}
