use crate::{duration::Duration, DateRange, Period};
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
    periodicity: Period,
    current_date: Date,
    pub(crate) len: i32,
}

impl Timeline {
    pub fn new(range: DateRange, periodicity: Period) -> Self {
        let len = match periodicity {
            Period::Day => range.as_days(),
            Period::Week => range.as_weeks(true),
            Period::Month => range.as_months(true),
            Period::Quarter => range.as_quarters(true),
            Period::Year => range.as_years(true),
        };
        Timeline {
            range,
            periodicity,
            current_date: range.from(),
            len,
        }
    }

    pub fn change_periodicity(&self, new: Period) -> Self {
        Timeline::new(self.range, new)
    }

    pub fn index_at(self, date: Date) -> Option<i32> {
        if !self.range.contains(date) {
            return None;
        }
        let tmp_range = DateRange::new(self.range.from, date);
        match self.periodicity {
            Period::Day => Some(tmp_range.as_days()),
            Period::Week => Some(tmp_range.as_weeks(false)),
            Period::Month => Some(tmp_range.as_months(false)),
            Period::Quarter => Some(tmp_range.as_quarters(false)),
            Period::Year => Some(tmp_range.as_years(false)),
        }
    }

    pub fn index(&self, idx: i32) -> Option<DateRange> {
        if idx >= self.len {
            return None;
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
        let start = (self.range.from + dur1).primary();
        let end = cmp::min((start + dur2).primary(), self.range.to);
        Some(DateRange::new(start, end))
    }

    // TODO: write the following:
    //  * a getter for a time slice (maybe? need to think of the use case)

    // TODO: even needed?
    pub fn merge(self, other: Timeline) -> Result<Option<Timeline>, &'static str> {
        if self == other {
            return Ok(None);
        }
        if self.periodicity != other.periodicity {
            return Err("Time periods do match");
        }
        Ok(Some(Timeline::new(
            self.range.union(&other.range),
            self.periodicity,
        )))
    }
}

impl Iterator for Timeline {
    type Item = DateRange;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current_date == self.range.to() {
            return None;
        }

        let mut next_date = self.current_date;
        match self.periodicity {
            Period::Day => {
                next_date = match next_date.next_day() {
                    Some(d) => d,
                    None => {
                        return None;
                    }
                }
            }
            Period::Week => {
                for _ in 1..8 {
                    next_date = match next_date.next_day() {
                        Some(d) => d,
                        None => {
                            return None;
                        }
                    }
                }
            }
            Period::Month => {
                let (mut y, mut m, mut d) = next_date.to_calendar_date();
                m = m.next();
                if m == Month::January {
                    y += 1
                };
                d = cmp::min(days_in_year_month(y, m), d);
                next_date = match Date::from_calendar_date(y, m, d) {
                    Ok(d) => d,
                    Err(_) => {
                        return None;
                    }
                }
            }
            Period::Quarter => {
                let (mut y, mut m, mut d) = next_date.to_calendar_date();
                for _ in 1..4 {
                    m = m.next();
                    if m == Month::January {
                        y += 1
                    };
                }
                d = cmp::min(days_in_year_month(y, m), d);
                next_date = match Date::from_calendar_date(y, m, d) {
                    Ok(d) => d,
                    Err(_) => {
                        return None;
                    }
                }
            }
            Period::Year => {
                let (y, m, d) = next_date.to_calendar_date();
                next_date = match Date::from_calendar_date(y + 1, m, d) {
                    Ok(d) => d,
                    Err(_) => {
                        return None;
                    }
                }
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
        let tl = Timeline::new(dr, Period::Quarter);
        let mut i = 0;
        for test_range in tl {
            assert_eq!(test_range.to().year(), 2022);
            i += 1;
            if i > 4 {
                break;
            }
        }
    }
}
