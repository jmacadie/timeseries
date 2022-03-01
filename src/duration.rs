use crate::{DateArithmeticOutput, TimeSeriesError};
use core::fmt;
use std::cmp;
use std::ops::{Add, Sub};
use time::{
    util::{days_in_year, days_in_year_month},
    Date, Month,
};

/// # Duration
///
/// A struct to hold & work with a duration interval that spans days,
/// months and years. The days and months parts are intended to hold the
/// fractional parts that cannot be represented by a higher time period
///
/// Durations can be negative, like [`time::Duration`], but unlike
/// [`core::time::Duration`]
///
/// A duration can vary depending on the date it is measured from. For
/// example, 4 days on from 27th Feb 2021 is 4th Mar. But the same 4 days
/// on from the 27th Mar is 31st of the same month. This variation makes
/// it difficult to consistently work with durations between dates
///
/// The order of application of years, months and days **matters**.
/// In the forwards direction it is assumed that  periods are added
/// in the following order:
/// 1) years
/// 2) months
/// 3) days
///
/// However, after the addition of years and months it can be the case
/// that an invalid date has been arrived at. This occurs when a
/// "long" month date gets applied to a "short" month, normally when
/// the "from" day is the 31st, although February will restrict a few
/// days more. To solve the invalid intermediate date issue, and only when
/// this is found to occur, the day part diff will instead be done first.
/// Years then months will follow for this edge case.
///
/// If swapping the part application order also fails, for example when
/// there is no day part to the duration, then the intermediate date is
/// truncated to be end of month following the year/month move.
///
/// For negative durations, it is enforced that the duration parts are
/// kept the same as a forward duration between the two dates, i.e.
/// the duration that would be assessed if the order of the dates were
/// transposed. The consequence of this decision are that for negative
/// durations the order in which the parts are subtracted is reversed,
/// as comapred to a forward duration:
/// 1) days
/// 2) months
/// 3) years
///
/// A similar order transposition will occur if an invalid intermediate
/// date is arrived at
///
/// `Duration` can be added and subtracted from `Date`. It is asserted that
/// any addition of a `Duration` is reversable. This means that if you take
/// any `Date` and add a `Duration` then subtracting the same `Duration`
/// from the result will alwys bring you back to the initial `Date`. The
/// same holds if the `Duration` is subtracted first.
///
/// The above logic means that some dates can be arrived at from multiple
/// start dates and a given `Duration`. For example, the 29th Mar less 1
/// month is the 28th Feb, but so is the 28th Mar, the 30th Mar and the 31st
/// Mar. Therefore, 28th Feb plus 1 month is 28th Mar, 29th Mar, 30th Mar &
/// 31st Mar all at the same time!
///
/// To handle this ambigutity, `Date` and `Duration` aritmetic combinations
/// return a `DateArithmeticOutput` object rather than just a `Date`, as
/// might be expected. `DateArithmeticOutput` is a simple wrapper on a vector
/// of all the possible results from a `Date` and `Duration` arithmetic
/// combination. Often it will only hold one `Date`. The most likely `Date`
/// result can always be extracted from `DateArithmeticOutput` by calling the
/// `primary()` method
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Duration {
    days: i32,
    months: i32,
    years: i32,
}

impl Duration {
    // region: constructors
    /// Create a new `Duration`
    ///  
    /// Does not try to coerce the values as the correct coercion
    /// can only be determined with a reference date
    ///
    /// Subsequently use the `normalise()` method if you wish to coerce the
    /// values to a sensible range e.g. 365 days -> 1 year
    pub fn new(days: i32, months: i32, years: i32) -> Self {
        Self {
            days,
            months,
            years,
        }
    }

    /// Create a new `Duration` from a pair of dates
    ///
    /// The order of application of years, months and days **matters**.
    /// In the forwards direction it is assumed that  periods are added
    /// in the following order:
    /// 1) years
    /// 2) months
    /// 3) days
    ///
    /// However, after the addition of years and months it can be the case
    /// that an invalid date has been arrived at. This occurs when a
    /// "long" month date gets applied to a "short" month, normally when
    /// the "from" day is the 31st, although February will restrict a few
    /// days more. To solve the invalid intermediate date issue, and only when
    /// this is found to occur, the day part diff will instead be done first.
    /// Years then months will follow for this edge case.
    ///
    /// If swapping the part application order also fails, for example when
    /// there is no day part to the duration, then the intermediate date is
    /// truncated to be end of month following the year/month move.
    ///
    /// For negative durations, it is enforced that the duration parts are
    /// kept the same as a forward duration between the two dates, i.e.
    /// the duration that would be assessed if the order of the dates were
    /// transposed. The consequence of this decision are that for negative
    /// durations the order in which the parts are subtracted is reversed,
    /// as comapred to a forward duration:
    /// 1) days
    /// 2) months
    /// 3) years
    ///
    /// A similar order transposition will occur if an invalid intermediate
    /// date is arrived at
    pub fn from_dates(from: Date, to: Date) -> Self {
        // If dates ordered with from before to, then just run a normal
        // duration calc
        if to > from {
            return Self::from_dates_pos(from, to);
        }

        // Here dates ordered the other way around: calculate the duration
        // the right way around and then reverse the sign of all the parts
        Self::from_dates_pos(to, from).invert()
    }

    /// Create a new `Duration` from a [`time::Duration`] object
    pub fn from_time_duration(dur: time::Duration) -> Result<Self, TimeSeriesError> {
        let days = dur.whole_days();
        let days = i32::try_from(days).map_err(|_| TimeSeriesError::TimeDurationTooLarge)?;
        Ok(Self::new(days, 0, 0))
    }

    /// Internal method for calculating a `Duration` from a pair
    /// of dates. Used by the `from_dates()` method. This method
    /// only works on dates in a postive direction i.e. the `from`
    /// date is before the `to` date
    fn from_dates_pos(from: Date, to: Date) -> Self {
        let mut years = to.year() - from.year();
        let mut months = to.month() as i32 - from.month() as i32;
        let mut days = to.day() as i32 - from.day() as i32;

        let (y, m) = Self::coerce_ym(years, months, days);
        months = m;
        years = y;

        if days < 0 {
            let (m2, d) = Self::coerce_md(months, from, to);
            months = m2;
            days = d;
        }
        Self::new(days, months, years)
    }

    /// Fix years and months to valid, consistent ranges
    fn coerce_ym(mut years: i32, mut months: i32, days: i32) -> (i32, i32) {
        if years > 0 && (months < 0 || (months == 0 && days < 0)) {
            years -= 1;
            months += 12;
        }
        (years, months)
    }

    /// Fix months and days to valid ranges
    ///
    /// Months are positive and days are negative
    fn coerce_md(mut months: i32, from: Date, to: Date) -> (i32, i32) {
        // Months will be in range 1..=12

        months -= 1;

        let temp_date: Date;
        let temp_year: i32;
        let temp_month: Month;
        let temp_day: u8;
        let days: i32;

        temp_day = from.day();
        temp_month = to.month().previous();
        temp_year = match temp_month {
            Month::December => to.year() - 1,
            _ => to.year(),
        };

        temp_date = match Date::from_calendar_date(temp_year, temp_month, temp_day) {
            Ok(d) => d,
            Err(_) => {
                // If we have an error then we couldn't get to a real date by adding years and months first.
                // It means we had a long month day (generally 31) and tried to match it to a short month
                // Instead need to add enough days to the from date to get to the first day of the next
                // month before we consider the month or the year move
                // If we have this, the day diff can be calculated directly and we can return straight out
                days = to.day() as i32 + days_in_year_month(from.year(), from.month()) as i32
                    - from.day() as i32
                    + 1;
                return (months, days);
            }
        };

        days = match temp_month {
            Month::December => {
                to.ordinal() as i32 - temp_date.ordinal() as i32 + days_in_year(temp_year) as i32
            }
            _ => to.ordinal() as i32 - temp_date.ordinal() as i32,
        };
        (months, days)
    }
    // endregion constructors

    // region: getters
    pub fn days(&self) -> i32 {
        self.days
    }

    pub fn months(&self) -> i32 {
        self.months
    }

    pub fn years(&self) -> i32 {
        self.years
    }
    // endregion getters

    // region: utility methods
    /// Function to convert an overflowing duration created by a new
    /// call into a normalise days, months and years duration.
    /// By normalised it is meant that days are in the range 0..32 &
    /// months are in the range  0..13
    pub fn normalise(&self, date: Date) -> Result<Self, TimeSeriesError> {
        let to = (date + self)?.primary();
        Ok(Self::from_dates(date, to))
    }

    /// Inverts a duration by changing the sign on every part of the duration
    pub fn invert(&self) -> Self {
        let days = -self.days;
        let months = -self.months;
        let years = -self.years;
        Duration {
            days,
            months,
            years,
        }
    }

    /// Convert the duration to an approximate number of days.
    /// Isn't perfect as to get this right you'd need to know which reference
    /// date you're starting from
    pub fn size(&self) -> f64 {
        self.years as f64 * 365.25 + self.months as f64 * 365.25 / 12_f64 + self.days as f64
    }

    /// Is the direction of the duration forwards in time?
    /// False implies it's backwards in time.
    ///
    /// Because this relies on size()
    /// it's possible that for weird mixed sign durations this could be
    /// wrong when the duration is close to zero. CBA to code for this as
    /// no one using this sanely should be doing this.
    pub fn forwards(&self) -> bool {
        self.size() > 0_f64
    }
    // endregion utility methods

    // region: addition
    /// Root internal method for performing addition.
    /// Called by the trait implementations which consider the
    /// various combinations of adding and subtracting Dates and
    /// Durations
    fn add_int(dur: Duration, date: Date) -> Result<DateArithmeticOutput, TimeSeriesError> {
        // Add days first for negative durations & last for positive
        let days_first = !dur.forwards();

        let mut output = dur.add_once(date, days_first, true)?;

        // Add the other days that could result from the addition / subtraction
        if dur.is_multiple_output(date)? {
            // Deal with days that could have multiplied because both routes give rise to
            // an invalid date, so the invalid date is truncated to month end
            // Only ever happens at end of month
            if Self::is_eom(date) {
                let day = date.day() as i32 + cmp::max(dur.days, 0) + 1;
                let (year, month) = dur.add_ym(date);
                let lim = days_in_year_month(year, month) as i32 + cmp::min(dur.days, 0) + 1;
                for i in day..lim {
                    // N.B. might never loop here & that's OK
                    let temp = i as u8;
                    if let Ok(d) = Date::from_calendar_date(year, month, temp) {
                        output.append(d);
                    }
                }
            }

            // Check for date by adding with the days order reversed
            let d = dur.add_once(date, !days_first, false)?.primary();
            if !output.contains(d) {
                output.append(d);
            }
        }
        Ok(output)
    }

    /// Determine if the date plus duration will give rise to multiple outputs
    fn is_multiple_output(&self, date: Date) -> Result<bool, TimeSeriesError> {
        let temp: Date;
        let day_lim: i32;

        if self.forwards() {
            temp = date;
            day_lim = self.days;
        } else {
            temp = self.add_days(date)?;
            day_lim = 1 - self.days;
        }

        let (year, month) = self.add_ym(temp);
        let to = days_in_year_month(year, month) as i32;
        let from = days_in_year_month(temp.year(), temp.month()) as i32;

        Ok(temp.day() as i32 > from - cmp::min(cmp::max(to - from, 0), cmp::max(day_lim, 1)))
    }

    /// Is the date at the end of the month?
    fn is_eom(date: Date) -> bool {
        date.day() == days_in_year_month(date.year(), date.month())
    }

    /// Add years and months to a date, wrapping month overflows into
    /// additional years. Return a tuple of the resultant year and month
    fn add_ym(&self, date: Date) -> (i32, Month) {
        // Overflowing add on the year and month part
        let mut year = date.year() + self.years;
        let mut month = date.month() as i32 + self.months;

        // Deal with month overflows
        // Months are on the range 1..13, so need to shift by 1 in & out to get logic for end points right
        month -= 1;
        year += month / 12;
        month %= 12;
        if month < 0 {
            month += 12;
            year -= 1;
        }
        month += 1;
        // I'm pretty confident we'll never get an error
        // on the try_from. Used unwrap_or with a default
        // value, so that we remove the chance for panicing
        // code, although this does introduce the risk that
        // I'm wrong and we have a silent error!
        let month = Month::try_from(month as u8).unwrap_or(Month::January);

        (year, month)
    }

    /// Internal method for addition. Allows us to try days first or second and if it
    /// fails, the other way around.
    ///
    /// If the other way round also fails, will truncate
    /// the failing intermediate date to end of month
    fn add_once(
        &self,
        date: Date,
        days_first: bool,
        first_pass: bool,
    ) -> Result<DateArithmeticOutput, TimeSeriesError> {
        // Assign the internal date variable & add days, if that's what we're doing
        let mut temp: Date;
        if days_first {
            temp = self.add_days(date)?;
        } else {
            temp = date;
        }
        let day = temp.day();

        let (year, month) = self.add_ym(temp);

        // Try to create the intermediate date
        temp = match Date::from_calendar_date(year, month, day) {
            Ok(d) => d,
            Err(_) => {
                if !first_pass {
                    // If all else fails then take the day at the end of the month being tried
                    let d = Date::from_calendar_date(year, month, days_in_year_month(year, month))
                        .unwrap_or(date);
                    return Ok(DateArithmeticOutput::new(d));
                }
                return self.add_once(date, !days_first, false);
            }
        };

        // Add days as required
        if !days_first {
            temp = self.add_days(temp)?;
        }
        Ok(DateArithmeticOutput::new(temp))
    }

    /// Internal method to add any number of days to a date
    fn add_days(&self, date: Date) -> Result<Date, TimeSeriesError> {
        let julian = date.to_julian_day() + self.days;
        let d = Date::from_julian_day(julian).map_err(|_| TimeSeriesError::DateOutOfRange)?;
        Ok(d)
    }
    // endregion addition
}

// region: trait implementaions
impl Add for Duration {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let years = self.years + other.years;
        let months = self.months as i32 + other.months as i32;
        let days = self.days as i32 + other.days as i32;
        Duration::new(days, months, years)
    }
}

impl Add<Date> for Duration {
    type Output = Result<DateArithmeticOutput, TimeSeriesError>;

    fn add(self, rhs: Date) -> Result<DateArithmeticOutput, TimeSeriesError> {
        Self::add_int(self, rhs)
    }
}

impl Add<Duration> for Date {
    type Output = Result<DateArithmeticOutput, TimeSeriesError>;

    fn add(self, rhs: Duration) -> Result<DateArithmeticOutput, TimeSeriesError> {
        Duration::add_int(rhs, self)
    }
}

impl Add<&Duration> for Date {
    type Output = Result<DateArithmeticOutput, TimeSeriesError>;

    fn add(self, rhs: &Duration) -> Result<DateArithmeticOutput, TimeSeriesError> {
        Duration::add_int(*rhs, self)
    }
}

impl Add<Duration> for DateArithmeticOutput {
    type Output = Result<DateArithmeticOutput, TimeSeriesError>;

    fn add(self, rhs: Duration) -> Result<DateArithmeticOutput, TimeSeriesError> {
        // TODO: add up all the values not just the primary one
        Duration::add_int(rhs, self.primary())
    }
}

impl Sub for Duration {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        let years = self.years - other.years;
        let months = self.months as i32 - other.months as i32;
        let days = self.days as i32 - other.days as i32;
        Duration::new(days, months, years)
    }
}

impl Sub<Duration> for Date {
    type Output = Result<DateArithmeticOutput, TimeSeriesError>;

    fn sub(self, rhs: Duration) -> Result<DateArithmeticOutput, TimeSeriesError> {
        Duration::add_int(rhs.invert(), self)
    }
}

impl Sub<Duration> for DateArithmeticOutput {
    type Output = Result<DateArithmeticOutput, TimeSeriesError>;

    fn sub(self, rhs: Duration) -> Result<DateArithmeticOutput, TimeSeriesError> {
        // TODO: add up all the values not just the primary one
        Duration::add_int(rhs.invert(), self.primary())
    }
}
// endregion trait implementations

// region: formatting
impl fmt::Display for Duration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut out = String::new();
        if self.years == 1 {
            out.push_str(&"1 year".to_string());
        } else if self.years != 0 {
            out.push_str(&format!("{} years", self.years));
        }
        if !out.is_empty() && self.months != 0 {
            out.push_str(", ");
        }
        if self.months == 1 {
            out.push_str(&"1 month".to_string());
        } else if self.months != 0 {
            out.push_str(&format!("{} months", self.months));
        }
        if !out.is_empty() && self.days != 0 {
            out.push_str(", ");
        }
        if self.days == 1 {
            out.push_str(&"1 day".to_string());
        } else if self.days != 0 {
            out.push_str(&format!("{} days", self.days));
        }
        f.write_str(&out)
    }
}
// endregion formatting

#[cfg(test)]
mod tests {

    use time::{Date, Month};

    use super::*;

    #[test]
    fn create_duration() {
        // Create a simple duration
        let mut d = Duration::new(1, 2, 3);
        assert_eq!((d.days(), d.months(), d.years()), (1, 2, 3));

        // Create durations with mixed signs
        d = Duration::new(1, -2, 3);
        assert_eq!((d.days(), d.months(), d.years()), (1, -2, 3));

        d = Duration::new(1, 2, -3);
        assert_eq!((d.days(), d.months(), d.years()), (1, 2, -3));

        d = Duration::new(-1, 2, 3);
        assert_eq!((d.days(), d.months(), d.years()), (-1, 2, 3));

        // Create durations with overflows
        d = Duration::new(64, 0, 1);
        assert_eq!((d.days(), d.months(), d.years()), (64, 0, 1));

        d = Duration::new(64, 10, 1);
        assert_eq!((d.days(), d.months(), d.years()), (64, 10, 1));
    }

    #[test]
    fn create_duration_from_dates() {
        // Create a simple duration
        let mut from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let mut to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let mut d = Duration::from_dates(from, to);
        assert_eq!((d.days(), d.months(), d.years()), (0, 0, 1));

        // Do it in reverse, do we get the opposite?
        d = Duration::from_dates(to, from);
        assert_eq!((d.days(), d.months(), d.years()), (0, 0, -1));

        // Test with sign corrections
        to = Date::from_calendar_date(2023, Month::January, 9).unwrap();
        d = Duration::from_dates(from, to);
        assert_eq!((d.days(), d.months(), d.years()), (30, 11, 0));

        // Test February
        from = Date::from_calendar_date(2023, Month::February, 27).unwrap();
        to = Date::from_calendar_date(2023, Month::March, 2).unwrap();
        d = Duration::from_dates(from, to);
        assert_eq!((d.days(), d.months(), d.years()), (3, 0, 0));

        // Test February in a leap year
        from = Date::from_calendar_date(2024, Month::February, 27).unwrap();
        to = Date::from_calendar_date(2024, Month::March, 2).unwrap();
        d = Duration::from_dates(from, to);
        assert_eq!((d.days(), d.months(), d.years()), (4, 0, 0));

        // Test February plus a year in a leap year
        from = Date::from_calendar_date(2023, Month::February, 27).unwrap();
        to = Date::from_calendar_date(2024, Month::March, 2).unwrap();
        d = Duration::from_dates(from, to);
        assert_eq!((d.days(), d.months(), d.years()), (4, 0, 1));

        // Test February plus a year in a leap year, in reverse
        // The leap year still counts as in reverse, effectively days comes first
        d = Duration::from_dates(to, from);
        assert_eq!((d.days(), d.months(), d.years()), (-4, 0, -1));

        // Test over a year end
        from = Date::from_calendar_date(2023, Month::December, 27).unwrap();
        to = Date::from_calendar_date(2024, Month::January, 2).unwrap();
        d = Duration::from_dates(from, to);
        assert_eq!((d.days(), d.months(), d.years()), (6, 0, 0));

        // ... and back the other way over the year end
        d = Duration::from_dates(to, from);
        assert_eq!((d.days(), d.months(), d.years()), (-6, 0, 0));

        // Test over a year end
        from = Date::from_calendar_date(2023, Month::October, 27).unwrap();
        to = Date::from_calendar_date(2026, Month::February, 15).unwrap();
        d = Duration::from_dates(from, to);
        assert_eq!((d.days(), d.months(), d.years()), (19, 3, 2));

        // ... and back the other way over the year end
        d = Duration::from_dates(to, from);
        assert_eq!((d.days(), d.months(), d.years()), (-19, -3, -2));

        // Test from "long" month to "short" month
        from = Date::from_calendar_date(2022, Month::October, 31).unwrap();
        to = Date::from_calendar_date(2022, Month::November, 30).unwrap();
        d = Duration::from_dates(from, to);
        assert_eq!((d.days(), d.months(), d.years()), (30, 0, 0));

        // Test from "short" month to "long" month
        from = Date::from_calendar_date(2022, Month::February, 28).unwrap();
        to = Date::from_calendar_date(2022, Month::April, 30).unwrap();
        d = Duration::from_dates(from, to);
        assert_eq!((d.days(), d.months(), d.years()), (2, 2, 0));

        // Test where temp date could try a missing date
        from = Date::from_calendar_date(2022, Month::October, 31).unwrap();
        to = Date::from_calendar_date(2022, Month::December, 15).unwrap();
        d = Duration::from_dates(from, to);
        assert_eq!((d.days(), d.months(), d.years()), (16, 1, 0));
    }

    #[test]
    fn create_from_duration() {
        let mut td = time::Duration::seconds_f64(10.0);
        let mut d = crate::duration::Duration::from_time_duration(td).unwrap();
        assert_eq!((d.days(), d.months(), d.years()), (0, 0, 0));

        td = time::Duration::seconds_f64(60.0 * 60.0 * 24.0);
        d = crate::duration::Duration::from_time_duration(td).unwrap();
        assert_eq!((d.days(), d.months(), d.years()), (1, 0, 0));

        td = time::Duration::seconds_f64(40.0 * 60.0 * 60.0 * 24.0);
        d = crate::duration::Duration::from_time_duration(td).unwrap();
        assert_eq!((d.days(), d.months(), d.years()), (40, 0, 0));

        // Test for value above i32 range
        td = time::Duration::seconds_f64(2_147_483_648.0 * 60.0 * 60.0 * 24.0);
        let e = crate::duration::Duration::from_time_duration(td);
        assert!(e.is_err());
    }

    #[test]
    fn add_duration() {
        let d1 = Duration::new(1, 2, 3);
        let d2 = Duration::new(100, 20, 50);
        let d3 = Duration::new(-10, -43, -12);

        // Test simple add
        let mut d = d1 + d2;
        assert_eq!((d.days(), d.months(), d.years()), (101, 22, 53));

        // Test commutativity
        d = d2 + d1;
        assert_eq!((d.days(), d.months(), d.years()), (101, 22, 53));

        // Test other adds
        d = d1 + d3;
        assert_eq!((d.days(), d.months(), d.years()), (-9, -41, -9));
        d = d2 + d3;
        assert_eq!((d.days(), d.months(), d.years()), (90, -23, 38));
    }

    #[test]
    fn sub_duration() {
        let d1 = Duration::new(1, 2, 3);
        let d2 = Duration::new(100, 20, 50);
        let d3 = Duration::new(-10, -43, -12);

        // Test simple sub
        let mut d = d1 - d2;
        assert_eq!((d.days(), d.months(), d.years()), (-99, -18, -47));

        // Test other subs
        d = d1 - d3;
        assert_eq!((d.days(), d.months(), d.years()), (11, 45, 15));
        d = d3 - d2;
        assert_eq!((d.days(), d.months(), d.years()), (-110, -63, -62));
    }

    #[test]
    fn add_date_duration() {
        // Create a simple duration
        let mut date = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let mut duration = Duration::new(1, 2, 3);

        // Test the addition is ok
        let mut d = (date + duration).unwrap().primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2025, 3, 11));

        // Add a negative duration
        duration = Duration::new(-1, 0, 0);
        d = (date + duration).unwrap().primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2022, 1, 9));

        // Add a negative wrap over year end
        duration = Duration::new(-10, 0, -1);
        d = (date + duration).unwrap().primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2020, 12, 31));

        // Add a negative wrap over year end, with possible bad intermediate date
        duration = Duration::new(-10, -1, -1);
        d = (date + duration).unwrap().primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2020, 11, 30));

        // Try a day overflowing add
        duration = Duration::new(50, 0, 0);
        d = (date + duration).unwrap().primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2022, 3, 1));

        // Try a month overflowing add
        duration = Duration::new(0, 30, 0);
        d = (date + duration).unwrap().primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2024, 7, 10));

        // Try a day overflowing add of negative number
        duration = Duration::new(-50, 0, 0);
        d = (date + duration).unwrap().primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2021, 11, 21));

        // Try a month overflowing add of negative number
        duration = Duration::new(0, -30, 0);
        d = (date + duration).unwrap().primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2019, 7, 10));

        // Try a day overflowing add + leap year
        duration = Duration::new(50, 0, 0);
        date = Date::from_calendar_date(2024, Month::January, 10).unwrap();
        d = (date + duration).unwrap().primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2024, 2, 29));
    }

    #[test]
    fn add_duration_date() {
        // Create a simple duration
        let date = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let mut duration = Duration::new(1, 2, 3);

        // Test the addition is ok
        let mut d = (duration + date).unwrap().primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2025, 3, 11));

        // Add a negative duration
        duration = Duration::new(-1, 0, 0);
        d = (duration + date).unwrap().primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2022, 1, 9));
    }

    #[test]
    fn sub_date_duration() {
        // Create a simple duration
        let mut date = Date::from_calendar_date(2022, Month::December, 10).unwrap();
        let mut duration = Duration::new(1, 2, 3);

        // Test the subtraction is ok
        let mut d = (date - duration).unwrap().primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2019, 10, 9));

        // Subtraction a negative duration
        duration = Duration::new(-1, 0, 0);
        d = (date - duration).unwrap().primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2022, 12, 11));

        // Subtraction a negative wrap over year end
        duration = Duration::new(-25, 0, -1);
        d = (date - duration).unwrap().primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2024, 1, 4));

        // Subtraction a negative wrap over year end, with possible bad intermediate date
        date = Date::from_calendar_date(2022, Month::December, 31).unwrap();
        duration = Duration::new(-10, -2, -1);
        d = (date - duration).unwrap().primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2024, 3, 10));

        // Try a day overflowing subtraction
        date = Date::from_calendar_date(2022, Month::December, 10).unwrap();
        duration = Duration::new(50, 0, 0);
        d = (date - duration).unwrap().primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2022, 10, 21));

        // Try a month overflowing subtraction
        duration = Duration::new(0, 30, 0);
        d = (date - duration).unwrap().primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2020, 6, 10));

        // Try a day overflowing subtraction of negative number
        duration = Duration::new(-81, 0, 0);
        d = (date - duration).unwrap().primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2023, 3, 1));

        // Try a month overflowing subtraction of negative number
        duration = Duration::new(0, -30, 0);
        d = (date - duration).unwrap().primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2025, 6, 10));

        // Try a day overflowing subtraction + leap year
        duration = Duration::new(50, 0, 0);
        date = Date::from_calendar_date(2024, Month::March, 10).unwrap();
        d = (date - duration).unwrap().primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2024, 1, 20));
    }

    #[test]
    fn all_add_results() {
        let mut d: Date;
        let mut t: Date;
        let mut dur: Duration;
        let mut res: DateArithmeticOutput;

        // TODO: write some more. Just put in a particular edge case for now

        // Crazy but true
        d = Date::from_calendar_date(2022, Month::February, 28).unwrap();
        dur = Duration::new(2, 3, 0);
        res = (d + dur).unwrap();
        t = Date::from_calendar_date(2022, Month::May, 29).unwrap();
        assert!(!res.contains(t));
        t = Date::from_calendar_date(2022, Month::May, 30).unwrap();
        assert!(res.contains(t));
        t = Date::from_calendar_date(2022, Month::May, 31).unwrap();
        assert!(res.contains(t));
        t = Date::from_calendar_date(2022, Month::June, 1).unwrap();
        assert!(!res.contains(t));
        t = Date::from_calendar_date(2022, Month::June, 2).unwrap();
        assert!(res.contains(t));
        t = Date::from_calendar_date(2022, Month::June, 3).unwrap();
        assert!(!res.contains(t));

        // Crazy but true
        d = Date::from_calendar_date(2022, Month::February, 27).unwrap();
        dur = Duration::new(2, 3, 0);
        res = (d + dur).unwrap();
        t = Date::from_calendar_date(2022, Month::May, 29).unwrap();
        assert!(res.contains(t));
        t = Date::from_calendar_date(2022, Month::May, 30).unwrap();
        assert!(!res.contains(t));
        t = Date::from_calendar_date(2022, Month::May, 31).unwrap();
        assert!(!res.contains(t));
        t = Date::from_calendar_date(2022, Month::June, 1).unwrap();
        assert!(res.contains(t));
        t = Date::from_calendar_date(2022, Month::June, 2).unwrap();
        assert!(!res.contains(t));
        t = Date::from_calendar_date(2022, Month::June, 3).unwrap();
        assert!(!res.contains(t));
    }

    #[test]
    fn add_and_sub_duration() {
        // Test that adding and subtracting the same interval always gets back to the same start date

        /*let mut d1: Date;
        let mut d2: Date;
        let mut d3: DateArithmeticOutput;
        let mut dur: Duration;
        let mut test: bool;
        let addition: bool = true;

        for day in 0..10 {
            println!("");
            println!("Day {}", day);
            println!("------");
            d1 = Date::from_calendar_date(2022, Month::January, 1).unwrap();
            dur = Duration::new(day, 3, 0);
            for _ in 0..365 {
                if let Some(d) = d1.next_day() { d1 = d; }
                if addition {
                    d2 = (d1 - dur).primary();
                    d3 = d2 + dur;
                    test = dur.is_multiple_output(d2);
                } else {
                    d2 = (d1 + dur).primary();
                    d3 = d2 - dur;
                    test = dur.invert().is_multiple_output(d2);
                }
                if d1 != d3.primary() || test {
                    if addition {
                        println!("{}: {} plus {} => {}", d1, d2, dur, d3);
                    } else {
                        println!("{}: {} minus {} => {}", d1, d2, dur, d3);
                    }
                }
            }
        }
        assert_eq!(1, 2);*/

        let mut d1: Date;
        let mut d2: DateArithmeticOutput;
        let mut dur: Duration;

        for month in 0..13 {
            for day in 0..10 {
                d1 = Date::from_calendar_date(2022, Month::January, 1).unwrap();
                dur = Duration::new(day, month, 0);
                for _ in 0..1500 {
                    // 4 years - will capture leap years
                    if let Some(d) = d1.next_day() {
                        d1 = d;
                    }
                    d2 = ((d1 - dur).unwrap() + dur).unwrap();
                    assert!(d2.contains(d1));
                    d2 = ((d1 + dur).unwrap() - dur).unwrap();
                    assert!(d2.contains(d1));
                }
            }
        }
    }

    #[test]
    fn normalise() {
        let dur = Duration::new(365, 0, 0);
        let mut tar = Duration::new(30, 11, 0);
        let mut date = Date::from_calendar_date(2024, Month::February, 25).unwrap();
        let mut res = dur.normalise(date).unwrap();
        assert_eq!(res, tar);

        tar = Duration::new(0, 0, 1);
        date = Date::from_calendar_date(2022, Month::February, 25).unwrap();
        res = dur.normalise(date).unwrap();
        assert_eq!(res, tar);
    }

    #[test]
    fn format() {
        let mut dur = Duration::new(1, 0, 0);
        assert_eq!(format!("{:}", dur), "1 day");

        dur = Duration::new(12, 0, 0);
        assert_eq!(format!("{:}", dur), "12 days");

        dur = Duration::new(0, 1, 0);
        assert_eq!(format!("{:}", dur), "1 month");

        dur = Duration::new(0, 5, 0);
        assert_eq!(format!("{:}", dur), "5 months");

        dur = Duration::new(0, 0, 1);
        assert_eq!(format!("{:}", dur), "1 year");

        dur = Duration::new(0, 0, 10);
        assert_eq!(format!("{:}", dur), "10 years");

        dur = Duration::new(2, 1, 0);
        assert_eq!(format!("{:}", dur), "1 month, 2 days");

        dur = Duration::new(1, 0, 4);
        assert_eq!(format!("{:}", dur), "4 years, 1 day");

        dur = Duration::new(0, 6, 1);
        assert_eq!(format!("{:}", dur), "1 year, 6 months");

        dur = Duration::new(1, 71, 4);
        assert_eq!(format!("{:}", dur), "4 years, 71 months, 1 day");
    }
}
