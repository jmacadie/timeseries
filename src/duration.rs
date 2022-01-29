use time::{Date, Month, util::{days_in_year, days_in_year_month}};
use std::ops::{Add, Sub};

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
    /// the "from" day is the 31st although February will restrict a few 
    /// days more. To solve the invalid intermediate date issue, & only when 
    /// this is found to occur, the day part diff will instead be done first.
    /// Years then months will follow for this edge case.
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
        Self::invert(Self::from_dates_pos(to, from))
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

    pub fn days(self) -> i32 {
        self.days
    }

    pub fn months(self) -> i32 {
        self.months
    }

    pub fn years(self) -> i32 {
        self.years
    }

    // Inverts a duration by changing the sign on every part of the duration
    fn invert(self) -> Self {
        let days = -self.days;
        let months = -self.months;
        let years = -self.years;
        Duration { days, months, years }
    }

    fn add(dur: Duration, date: Date) -> Result<Date, &'static str> {
        // Calculate the approx size of the duration
        let size = dur.years as f64 * 365.25
                        + dur.months as f64 * 30.5
                        + dur.days as f64;

        // Add days first for negative durations & last for positive
        let d: Date;
        if size > 0_f64 {
            d = Self::add_once(dur, date, false, true)?; 
        } else {
            d = Self::add_once(dur, date, true, true)?; 
        }
        Ok(d)
    }

    fn add_once(dur: Duration, date: Date, days_first: bool, first_pass: bool) -> Result<Date, &'static str> {
        
        // Assign the internal date variable - add days if that's what we're doing
        let mut temp: Date;
        if days_first {
            temp = Self::add_days(date, dur.days);
        } else {
            temp = date;
        }

        // Overflowing add on the year and month part
        let mut year = temp.year() + dur.years;
        let mut month = temp.month() as i32 + dur.months;
        let day = temp.day();

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

        // Try to create the intermediate date
        temp = match Date::from_calendar_date(year, month, day) {
            Ok(d) => d,
            Err(_) => {
                if !first_pass { return Err("Cannot add this duration to this date"); }
                let d = Self::add_once(dur, date, !days_first, false)?;
                return Ok(d);
            }
        };

        // Add days as required
        if !days_first {
            temp = Self::add_days(temp, dur.days);
        }

        Ok(temp)
    }
    
    fn add_days(date: Date, days: i32) -> Date {
        let julian = date.to_julian_day() + days;
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
    type Output = Result<Date, &'static str>;

    fn add(self, rhs: Date) -> Result<Date, &'static str> {
        Self::add(self, rhs)
    }

}

impl Add<Duration> for Date {
    type Output = Result<Date, &'static str>;

    fn add(self, rhs: Duration) -> Result<Date, &'static str> {
        Duration::add(rhs, self)
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
    type Output = Result<Date, &'static str>;

    fn sub(self, rhs: Duration) -> Result<Date, &'static str> {
        Duration::add(rhs.invert(), self)
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
        let d = date + duration;
        assert!(d.is_ok());
        
        // Check the result of the addition
        let mut d = d.unwrap();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2025, 3, 11));

        // Add a negative duration
        duration = Duration::new(-1, 0, 0);
        d = (date + duration).unwrap();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2022, 1, 9));

        // Add a negative wrap over year end
        duration = Duration::new(-10, 0, -1);
        d = (date + duration).unwrap();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2020, 12, 31));

        // Add a negative wrap over year end, with possible bad intermediate date
        duration = Duration::new(-10, -1, -1);
        d = (date + duration).unwrap();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2020, 11, 30));

        // Try a day overflowing add
        duration = Duration::new(50, 0, 0);
        d = (date + duration).unwrap();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2022, 3, 1));

        // Try a month overflowing add
        duration = Duration::new(0, 30, 0);
        d = (date + duration).unwrap();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2024, 7, 10));

        // Try a day overflowing add of negative number
        duration = Duration::new(-50, 0, 0);
        d = (date + duration).unwrap();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2021, 11, 21));

        // Try a month overflowing add of negative number
        duration = Duration::new(0, -30, 0);
        d = (date + duration).unwrap();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2019, 7, 10));

        // Try a day overflowing add + leap year
        duration = Duration::new(50, 0, 0);
        date = Date::from_calendar_date(2024, Month::January, 10).unwrap();
        d = (date + duration).unwrap();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2024, 2, 29));

    }

    #[test]
    fn add_duration_date() {

        // Create a simple duration
        let date = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let mut duration = Duration::new(1, 2, 3);

        // Test the addition is ok
        let d = duration + date;
        assert!(d.is_ok());
        
        // Check the result of the addition
        let mut d = d.unwrap();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2025, 3, 11));

        // Add a negative duration
        duration = Duration::new(-1, 0, 0);
        d = (duration + date).unwrap();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2022, 1, 9));
    }

    #[test]
    fn sub_date_duration() {

        // Create a simple duration
        let mut date = Date::from_calendar_date(2022, Month::December, 10).unwrap();
        let mut duration = Duration::new(1, 2, 3);

        // Test the subtraction is ok
        let d = date - duration;
        assert!(d.is_ok());
        
        // Check the result of the subtraction
        let mut d = d.unwrap();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2019, 10, 9));

        // Subtraction a negative duration
        duration = Duration::new(-1, 0, 0);
        d = (date - duration).unwrap();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2022, 12, 11));

        // Subtraction a negative wrap over year end
        duration = Duration::new(-25, 0, -1);
        d = (date - duration).unwrap();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2024, 1, 4));

        // Subtraction a negative wrap over year end, with possible bad intermediate date
        date = Date::from_calendar_date(2022, Month::December, 31).unwrap();
        duration = Duration::new(-10, -2, -1);
        d = (date - duration).unwrap();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2024, 3, 10));

        // Try a day overflowing subtraction
        date = Date::from_calendar_date(2022, Month::December, 10).unwrap();
        duration = Duration::new(50, 0, 0);
        d = (date - duration).unwrap();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2022, 10, 21));

        // Try a month overflowing subtraction
        duration = Duration::new(0, 30, 0);
        d = (date - duration).unwrap();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2020, 6, 10));

        // Try a day overflowing subtraction of negative number
        duration = Duration::new(-81, 0, 0);
        d = (date - duration).unwrap();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2023, 3, 1));

        // Try a month overflowing subtraction of negative number
        duration = Duration::new(0, -30, 0);
        d = (date - duration).unwrap();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2025, 6, 10));

        // Try a day overflowing subtraction + leap year
        duration = Duration::new(50, 0, 0);
        date = Date::from_calendar_date(2024, Month::March, 10).unwrap();
        d = (date - duration).unwrap();
        assert_eq!((d.year(), d.month() as u8, d.day()), (2024, 1, 20));

    }

}
