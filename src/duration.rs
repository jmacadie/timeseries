use crate::DateArithmeticOutput;
use time::{Date, Month, util::{days_in_year, days_in_year_month}};
use std::ops::{Add, Sub};
use std::cmp;
use core::fmt;

/// # Duration
/// 
/// A struct to hold & work with a duration interval that spans days,
/// months and years. The days and months parts will be held for the 
/// fractional parts that cannot be represented by a higher time period
/// 
/// Durations can be negative, like [`time::Duration`], but unlike
/// [`core::time::Duration`]
///
/// The days and months parts will be coerced into the correct fractional
/// parts with any overflowing amounts stored in the next higer period part:
/// * days will be held in the range -30 to 30 inclusive
/// * months will be held in the range -11 to 11 inclusive
///  
/// It is worth noting that because months can vary in length, the days 
/// fractional part could hold a value that is invalid when considered in 
/// conjuction with a given date. For example, there is no reasonable
/// representation of 30 days from 31<sup>st</sup> Jan and it would ideally be
/// collapsed down to 1 month and 1 or 2 days, depending on whether the year is
///  a leap year or not!
/// 
/// Because of the inconsistent relationship between days and months, it is
/// not possible to derive this object from [`time::Duration`], which only 
/// reliably works up to intervals of a week. [`time::Duration`] can hold many
/// days, which equate to time spans of well over a year, but it never attempts to
/// relate them into months and years, owing to this ambiguity
/// 
/// As a design decision this module will hold the day fractional part in a
/// manner that _could_ overflow into a months representation for certain 
/// start dates, which in turn means that there are multiple equivalent
/// `Duration`s between some pairs of specific dates. These specific dates,
/// which are at risk of have multiple `Duration` representations are
/// predominently end of month dates, which should be less common to work with.
/// It remains up to the user of this library to be aware of this inconsistency
/// and ensure this does not cause issues with thier code. Any inputs that use 
/// the overflow coercion are also at risk
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Duration {
    days: i32,   // will be on range -30..30 (inclusive)
    months: i32, // will be on range -11..11 (inclusive)
    years: i32, // will be any valid i32
}

impl Duration {

    /// Create a new `Duration` with length determined.
    ///  
    /// Do not try to coerce the values as the correct coercion
    /// can only be determined with a reference start or end 
    /// date
    pub fn new(days: i32, months: i32, years: i32) -> Self {
        Self { days, months, years }
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
        if to > from { return Self::from_dates_pos(from, to); }
        
        // Here dates ordered the other way around: calculate the duration
        // the right way around and then reverse the sign of all the parts
        Self::from_dates_pos(to, from).invert()
    }

    fn from_dates_pos(from: Date, to: Date) -> Self {

        let mut years = to.year() - from.year();
        let mut months = to.month() as i32 - from.month() as i32;
        let mut days = to.day() as i32 - from.day() as i32;

        //(years, months) = Duration::coerce_ym(years, months, days); // unstable feature!
        match Self::coerce_ym(years, months, days) {
            (y, m) => {
                years = y;
                months = m;
            }
        }

        if days < 0 {
            //(months, days) = Duration::coerce_md(months, days, from, to); // unstable feature!
            match Self::coerce_md (months, from, to) {
                (m, d) => {
                    months = m;
                    days = d;
                }
            }
        }
        Self::new(days, months, years)
    }

    /// Fix years and months to valid, consistent ranges
    fn coerce_ym(mut years: i32, mut months: i32, days: i32) -> (i32, i32) {
        if years > 0 &&
          (months < 0 || (months == 0 && days < 0)) {
              years -= 1;
              months += 12;
        }
        (years, months)
    }
    
    /// Fix months and days to valid ranges
    /// 
    /// Months are positive and days are negative
    fn coerce_md (mut months: i32, from: Date, to: Date) -> (i32, i32) {
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
                days = to.day() as i32
                       + days_in_year_month(from.year(), from.month()) as i32
                       - from.day() as i32
                       + 1;
                return (months, days);
            },
        };

        days = match temp_month {
            Month::December => {
                to.ordinal() as i32
                - temp_date.ordinal() as i32
                + days_in_year(temp_year) as i32
            },
            _ => {
                to.ordinal() as i32
                - temp_date.ordinal() as i32
            },
        };
        (months, days)
    }

    /// Function to convert an overflowing duration created by a new
    /// call into a normalise days, months and years duration.
    /// By normalised it is meant that days are in the range 0..32 &
    /// months are in the range  0..13
    pub fn normalise(&self, date: Date) -> Self {
        let to = (date + self).primary();
        Self::from_dates(date, to)
    }

    pub fn days(&self) -> i32 {
        self.days
    }

    pub fn months(&self) -> i32 {
        self.months
    }

    pub fn years(&self) -> i32 {
        self.years
    }

    /// Inverts a duration by changing the sign on every part of the duration
    fn invert(&self) -> Self {
        let days = -self.days;
        let months = -self.months;
        let years = -self.years;
        Duration { days, months, years }
    }

    fn add_int(dur: Duration, date: Date) -> DateArithmeticOutput {

        // Add days first for negative durations & last for positive
        let days_first: bool;
        if dur.forwards() {
            days_first = false;
        } else {
            days_first = true;
        }
        
        let mut output = dur.add_once(date, days_first, true);

        // Add the other days that could result from the addition / subtraction
        if dur.is_multiple_output(date) {

            // Deal with days that could have multiplied because both routes give rise to 
            // an invalid date, so the invalid date is truncated to month end
            // Only ever happens at end of month
            if Self::is_eom(date) {
                let day = date.day() as i32 + cmp::max(dur.days,0) + 1;
                let month;
                let year;
                match dur.add_ym(date) {
                    (y, m) => { year = y; month = m; }
                }
                let lim = days_in_year_month(year, month) as i32 + cmp::min(dur.days,0) + 1;
                for i in day..lim { // N.B. might never loop here & that's OK
                    let temp = i as u8;
                    output.append(Date::from_calendar_date(year, month, temp).unwrap());
                }
            }

            // Check for date by adding with the days order reversed
            let d = dur.add_once(date, !days_first, false).primary();
            if !output.contains(d) {
                output.append(d);
            }

        }
        output
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

    /// Convert the duration to an approximate number of days.
    /// Isn't perfect as to get this right you'd need to know which reference 
    /// date you're starting from
    pub fn size(&self) -> f64 {
        self.years as f64 * 365.25
            + self.months as f64 * 30.5
            + self.days as f64
    }

    /// Determine if the date plus duration will give rise to multiple outputs
    fn is_multiple_output(&self, date: Date) -> bool {
        
        let temp: Date;
        let day_lim: i32;

        if self.forwards() {
            temp = date;
            day_lim = self.days;
        } else {
            temp = self.add_days(date);
            day_lim = 1 - self.days;
        }
        
        let year: i32;
        let month: Month;

        match self.add_ym(temp) {
            (y, m) => {
                year = y;
                month = m;
            }
        }
        let to = days_in_year_month(year, month) as i32;
        let from = days_in_year_month(temp.year(), temp.month()) as i32;

        temp.day() as i32 >
            from
            - cmp::min(
                cmp::max(to - from, 0),
                cmp::max(day_lim, 1)
            )

    }

    /// Is the date at the end of the month?
    fn is_eom(date: Date) -> bool {
        return date.day() == days_in_year_month(date.year(), date.month());
    }

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
        let month = Month::try_from(month as u8).unwrap();

        (year, month)

    }

    /// Internal method for addition. Allows us to try days first or second and if it 
    /// fails, the other way around.
    /// 
    /// If the other way round also fails, will truncate
    /// the failing intermediate date to end of month
    fn add_once(&self, date: Date, days_first: bool, first_pass: bool) -> DateArithmeticOutput {
        
        // Assign the internal date variable & add days, if that's what we're doing
        let mut temp: Date;
        if days_first {
            temp = self.add_days(date);
        } else {
            temp = date;
        }
        let day = temp.day();

        let year: i32;
        let month: Month;
        match self.add_ym(temp) {
            (y, m) => {
                year = y;
                month = m;
            }
        }

        // Try to create the intermediate date
        temp = match Date::from_calendar_date(year, month, day) {
            Ok(d) => d,
            Err(_) => {
                if !first_pass { 
                    // If all else fails then take the day at the end of the month being tried
                    let d = Date::from_calendar_date(
                            year,
                            month, 
                            days_in_year_month(year, month)
                        ).unwrap();
                    return DateArithmeticOutput::new(d);
                }
                return self.add_once(date, !days_first, false);
            }
        };

        // Add days as required
        if !days_first {
            temp = self.add_days(temp);
        }
        DateArithmeticOutput::new(temp)
    }
    
    /// Internal method to add any number of days to a date
    fn add_days(&self, date: Date) -> Date {
        let julian = date.to_julian_day() + self.days;
        Date::from_julian_day(julian).unwrap()
    }

}

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
    type Output = DateArithmeticOutput;

    fn add(self, rhs: Date) -> DateArithmeticOutput {
        Self::add_int(self, rhs)
    }

}

impl Add<Duration> for Date {
    type Output = DateArithmeticOutput;

    fn add(self, rhs: Duration) -> DateArithmeticOutput {
        Duration::add_int(rhs, self)
    }

}

impl Add<&Duration> for Date {
    type Output = DateArithmeticOutput;

    fn add(self, rhs: &Duration) -> DateArithmeticOutput {
        Duration::add_int(*rhs, self)
    }

}

impl Add<Duration> for DateArithmeticOutput {
    type Output = DateArithmeticOutput;

    fn add(self, rhs: Duration) -> DateArithmeticOutput {
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
    type Output = DateArithmeticOutput;

    fn sub(self, rhs: Duration) -> DateArithmeticOutput {
        Duration::add_int(rhs.invert(), self)
    }

}

impl Sub<Duration> for DateArithmeticOutput {
    type Output = DateArithmeticOutput;

    fn sub(self, rhs: Duration) -> DateArithmeticOutput {
        // TODO: add up all the values not just the primary one
        Duration::add_int(rhs.invert(), self.primary())
    }

}

impl fmt::Display for Duration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut out = String::new();
        if self.years == 1 {
            out.push_str(&format!("1 year"));
        } else if self.years != 0 {
            out.push_str(&format!("{} years", self.years));
        }
        if out.len() > 0 && self.months != 0 {
            out.push_str(", ");
        }
        if self.months == 1 {
            out.push_str(&format!("1 month"));
        } else if self.months != 0 {
            out.push_str(&format!("{} months", self.months));
        }
        if out.len() > 0 && self.days != 0 {
            out.push_str(", ");
        }
        if self.days == 1 {
            out.push_str(&format!("1 day"));
        } else if self.days != 0 {
            out.push_str(&format!("{} days", self.days));
        }
        f.write_str(&out) 
    }
}

#[cfg(test)]
mod tests {

    use time::{Date, Month};

    use super::*;

    #[test]
    fn create_duration() {

        // Create a simple duration
        let mut d = Duration::new(1, 2 , 3);
        assert_eq!((d.days(), d.months(), d.years()), (1, 2, 3));

        // Create durations with mixed signs
        d = Duration::new(1, -2 , 3);
        assert_eq!((d.days(), d.months(), d.years()), (1, -2, 3));

        d = Duration::new(1, 2 , -3);
        assert_eq!((d.days(), d.months(), d.years()), (1, 2, -3));
        
        d = Duration::new(-1, 2 , 3);
        assert_eq!((d.days(), d.months(), d.years()), (-1, 2, 3));

        // Create durations with overflows
        d = Duration::new(64, 0 , 1);
        assert_eq!((d.days(), d.months(), d.years()), (64, 0, 1));

        d = Duration::new(64, 10 , 1);
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
        let mut d = (date + duration).primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2025, 3, 11));

        // Add a negative duration
        duration = Duration::new(-1, 0, 0);
        d = (date + duration).primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2022, 1, 9));

        // Add a negative wrap over year end
        duration = Duration::new(-10, 0, -1);
        d = (date + duration).primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2020, 12, 31));

        // Add a negative wrap over year end, with possible bad intermediate date
        duration = Duration::new(-10, -1, -1);
        d = (date + duration).primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2020, 11, 30));

        // Try a day overflowing add
        duration = Duration::new(50, 0, 0);
        d = (date + duration).primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2022, 3, 1));

        // Try a month overflowing add
        duration = Duration::new(0, 30, 0);
        d = (date + duration).primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2024, 7, 10));

        // Try a day overflowing add of negative number
        duration = Duration::new(-50, 0, 0);
        d = (date + duration).primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2021, 11, 21));

        // Try a month overflowing add of negative number
        duration = Duration::new(0, -30, 0);
        d = (date + duration).primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2019, 7, 10));

        // Try a day overflowing add + leap year
        duration = Duration::new(50, 0, 0);
        date = Date::from_calendar_date(2024, Month::January, 10).unwrap();
        d = (date + duration).primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2024, 2, 29));

    }

    #[test]
    fn add_duration_date() {

        // Create a simple duration
        let date = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let mut duration = Duration::new(1, 2, 3);

        // Test the addition is ok
        let mut d = (duration + date).primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2025, 3, 11));

        // Add a negative duration
        duration = Duration::new(-1, 0, 0);
        d = (duration + date).primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2022, 1, 9));
    }

    #[test]
    fn sub_date_duration() {

        // Create a simple duration
        let mut date = Date::from_calendar_date(2022, Month::December, 10).unwrap();
        let mut duration = Duration::new(1, 2, 3);

        // Test the subtraction is ok
        let mut d = (date - duration).primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2019, 10, 9));

        // Subtraction a negative duration
        duration = Duration::new(-1, 0, 0);
        d = (date - duration).primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2022, 12, 11));

        // Subtraction a negative wrap over year end
        duration = Duration::new(-25, 0, -1);
        d = (date - duration).primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2024, 1, 4));

        // Subtraction a negative wrap over year end, with possible bad intermediate date
        date = Date::from_calendar_date(2022, Month::December, 31).unwrap();
        duration = Duration::new(-10, -2, -1);
        d = (date - duration).primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2024, 3, 10));

        // Try a day overflowing subtraction
        date = Date::from_calendar_date(2022, Month::December, 10).unwrap();
        duration = Duration::new(50, 0, 0);
        d = (date - duration).primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2022, 10, 21));

        // Try a month overflowing subtraction
        duration = Duration::new(0, 30, 0);
        d = (date - duration).primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2020, 6, 10));

        // Try a day overflowing subtraction of negative number
        duration = Duration::new(-81, 0, 0);
        d = (date - duration).primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2023, 3, 1));

        // Try a month overflowing subtraction of negative number
        duration = Duration::new(0, -30, 0);
        d = (date - duration).primary();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2025, 6, 10));

        // Try a day overflowing subtraction + leap year
        duration = Duration::new(50, 0, 0);
        date = Date::from_calendar_date(2024, Month::March, 10).unwrap();
        d = (date - duration).primary();
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
        dur = Duration::new(2,3,0);
        res = d + dur;
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
        dur = Duration::new(2,3,0);
        res = d + dur;
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
                for _ in 0..1500 { // 4 years - will capture leap years
                    if let Some(d) = d1.next_day() { d1 = d; }
                    d2 = d1 - dur + dur;
                    assert!(d2.contains(d1));
                    d2 = d1 + dur - dur;
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
        let mut res = dur.normalise(date);
        assert_eq!(res, tar);
        
        tar = Duration::new(0, 0, 1);
        date = Date::from_calendar_date(2022, Month::February, 25).unwrap();
        res = dur.normalise(date);
        assert_eq!(res, tar);
    }

}
