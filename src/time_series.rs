use crate::timeline::TimeLine;
use std::ops::{Add, Sub, Mul, Div, Rem};

/// # TimeSeries
/// 
/// A compound object that holds both a timeline and an array of values that
/// meaningfully relate to the matching time periods from the timeline
/// 
/// The timeline is held by reference, as it is assumed that a common timeline
/// will apply to the entire model.
/// 
/// The values are a vector of any type.
/// 
/// TimeSeries objects are intended to be added, multiplied, subtracted and divided,
/// using pairwise arithmetic operations to every element across the timeline. For
/// this to work there are some requirements:
/// * the underlying value types must be the same in both TimeSeries objects. For
/// example, you cannot add integers to floats)
/// * the underlying value type must support the arithmetic operation. For example,
/// you cannot divide Strings and so you cannot divide TimeSeries of Strings
/// * the timelines of the two TimeSeries objects must be the same. This would not
/// normally be a problem in a common model where there is a single timeline for 
/// the entire model
/// 
/// It's also worth noting that these arithmetic operations have been implemented
/// on pointers to TimeSeries only. This is required as TimeSeries cannot implement
/// the `Copy` trait, due it's wrapping of a vector, which does not implement the
/// `Copy` trait. Without the `Copy` trait, all the arithmetic operations, and in fact
/// any function call, move the operands. This would mean that after `let c = a + b;` 
/// both `a` and `b` would no longer be available. Instead the only implemented operations
/// are on references, so `let c = &a + &b;`, which allows `a` and `b` to persist beyond
/// the addition call
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TimeSeries<'a, T> {
    pub(crate) timeline: &'a TimeLine,
    values: Vec<T>,
}

impl<'a, T> TimeSeries<'a, T> {

    /// Create a new TimeSeries object
    /// 
    /// This method will throw an error if the length of the timeline provided and the
    /// length of the value vector do not match
    pub fn new(timeline: &'a TimeLine, values: Vec<T>) -> Result<Self, &'static str> {
        match i32::try_from(values.len()) {
            Ok(l) => {
                if l != timeline.len { return Err("Values do not match the timeline"); }
            },
            Err(_) => {
                return Err("Couldn't convert length of values into i32");
            },
        }
        Ok(TimeSeries {
            timeline,
            values,
        })
    }

    // TODO: implement other ways of creating a TS object:
    //  * just provide some values and then pad out to full timeline

    // TODO: implement way to add values into an existing TS, maybe by providing a (Date, T) tuple

    // TODO: be able to cast the values vector to other types, inside a new TS

    // TODO: implement a way of combining two TS with the addition of user provided closure

    // TODO: implement getters
    //  * get single value at date
    //  * get slice of the underlying TS for a sub-date rate

    // TODO: implement a way of building corkscrews with multiple operations

}

impl<'a> TimeSeries<'a, i32> {
    
    /// For a given timline, create a TimeSeries of 32-bit integers, all with value 0
    pub fn empty_i(timeline: &'a TimeLine) -> TimeSeries<'a, i32> {
        let values = vec![0; timeline.len as usize];
        TimeSeries { timeline, values }
    }
}

impl<'a> TimeSeries<'a, f64> {
    
    /// For a given timline, create a TimeSeries of 64-bit floats, all with value 0
    pub fn empty_f(timeline: &'a TimeLine) -> TimeSeries<'a, f64> {
        let values = vec![0.0; timeline.len as usize];
        TimeSeries { timeline, values }
    }
}

impl<'a, 'b, 'c, T> Add<&'c TimeSeries<'a, T>> for &'b TimeSeries<'a, T>
    where T: Add + Add<Output = T> + Copy
{
    type Output = Result<TimeSeries<'a, T>, &'static str>;

    fn add(self, rhs: &'c TimeSeries<'a, T>) -> Result<TimeSeries<'a, T>, &'static str> {
        if self.timeline != rhs.timeline { return Err("Timelines do not match. Ensure a common timeline is being used"); }
        let data = self.values.iter()
            .zip(rhs.values.iter())
            .map(|(&a, &b)| a + b)
            .collect();
        // Went with unwrap here as a TimeSeries created in these conditions should always be OK
        Ok(TimeSeries::new(self.timeline, data).unwrap())
    }
}

impl<'a, 'b, 'c, T> Sub<&'c TimeSeries<'a, T>> for &'b TimeSeries<'a, T>
    where T: Sub + Sub<Output = T> + Copy
{
    type Output = Result<TimeSeries<'a, T>, &'static str>;

    fn sub(self, rhs: &'c TimeSeries<'a, T>) -> Result<TimeSeries<'a, T>, &'static str> {
        if self.timeline != rhs.timeline { return Err("Timelines do not match. Ensure a common timeline is being used"); }
        let data = self.values.iter()
            .zip(rhs.values.iter())
            .map(|(&a, &b)| a - b)
            .collect();
        // Went with unwrap here as a TimeSeries created in these conditions should always be OK
        Ok(TimeSeries::new(self.timeline, data).unwrap())
    }
}

impl<'a, 'b, 'c, T> Mul<&'c TimeSeries<'a, T>> for &'b TimeSeries<'a, T>
    where T: Mul + Mul<Output = T> + Copy
{
    type Output = Result<TimeSeries<'a, T>, &'static str>;

    fn mul(self, rhs: &'c TimeSeries<'a, T>) -> Result<TimeSeries<'a, T>, &'static str> {
        if self.timeline != rhs.timeline { return Err("Timelines do not match. Ensure a common timeline is being used"); }
        let data = self.values.iter()
            .zip(rhs.values.iter())
            .map(|(&a, &b)| a * b)
            .collect();
        // Went with unwrap here as a TimeSeries created in these conditions should always be OK
        Ok(TimeSeries::new(self.timeline, data).unwrap())
    }
}

impl<'a, 'b, 'c, T> Div<&'c TimeSeries<'a, T>> for &'b TimeSeries<'a, T>
    where T: Div + Div<Output = T> + Copy
{
    type Output = Result<TimeSeries<'a, T>, &'static str>;

    fn div(self, rhs: &'c TimeSeries<'a, T>) -> Result<TimeSeries<'a, T>, &'static str> {
        if self.timeline != rhs.timeline { return Err("Timelines do not match. Ensure a common timeline is being used"); }
        let data = self.values.iter()
            .zip(rhs.values.iter())
            .map(|(&a, &b)| a / b)
            .collect();
        // Went with unwrap here as a TimeSeries created in these conditions should always be OK
        Ok(TimeSeries::new(self.timeline, data).unwrap())
    }
}

impl<'a, 'b, 'c, T> Rem<&'c TimeSeries<'a, T>> for &'b TimeSeries<'a, T>
    where T: Rem + Rem<Output = T> + Copy
{
    type Output = Result<TimeSeries<'a, T>, &'static str>;

    fn rem(self, rhs: &'c TimeSeries<'a, T>) -> Result<TimeSeries<'a, T>, &'static str> {
        if self.timeline != rhs.timeline { return Err("Timelines do not match. Ensure a common timeline is being used"); }
        let data = self.values.iter()
            .zip(rhs.values.iter())
            .map(|(&a, &b)| a % b)
            .collect();
        // Went with unwrap here as a TimeSeries created in these conditions should always be OK
        Ok(TimeSeries::new(self.timeline, data).unwrap())
    }
}

// TODO: implement the OpAssign traits, such as AddAssign & DivAssign
// TODO: extend these operations to work with scalars as well

#[cfg(test)]
mod tests {

    use crate::{DateRange, Period};
    use time::{Date, Month};

    use super::*;

    #[test]
    fn create_timeseries() {

        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = TimeLine::new(dr, Period::Quarter);

        // Create timeseries, check ok
        let v1 = vec![1, 2, 3, 4];
        let ts1 = TimeSeries::new(&tl, v1);
        assert!(ts1.is_ok());

        // Create a timeseries of Strings (why?), check they're ok too
        let v2 = vec![
            String::from("a"),
            String::from("loerm ipsum"),
            String::from("hello, World!"),
            String::from("!£$%^&*()/|jkhsdaf`")];
        let ts2 = TimeSeries::new(&tl, v2);
        assert!(ts2.is_ok());

        // check the values in the timeseries are the same as we put in
        let ts1 = ts1.unwrap();
        assert_eq!(ts1.values, vec![1, 2, 3, 4]);
        let ts2 = ts2.unwrap();
        assert_eq!(ts2.values.len(), 4);
        assert_eq!(ts2.values[2], "hello, World!");

        // Create a timeseries with mismatched timeline and value, check for error
        let v3 = vec![1, 2, 3, 4, 5];
        let ts3 = TimeSeries::new(&tl, v3);
        assert!(ts3.is_err());

    }

    #[test]
    fn create_empty_timeseries() {
        
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = TimeLine::new(dr, Period::Quarter);

        // Create float and integer ts, check OK
        let ts_i = TimeSeries::empty_i(&tl);
        assert_eq!(ts_i.values, vec![0, 0, 0, 0]);
        let ts_f = TimeSeries::empty_f(&tl);
        assert_eq!(ts_f.values, vec![0.0, 0.0, 0.0, 0.0]);

    }

    #[test]
    fn add_timeseries() {
        
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = TimeLine::new(dr, Period::Quarter);

        // Create two timeseries
        let v1 = vec![1, 2, 3, 4];
        let ts1 = TimeSeries::new(&tl, v1).unwrap();
        let v2 = vec![5, 6, 7, 8];
        let ts2 = TimeSeries::new(&tl, v2).unwrap();

        // Add two TS and check OK
        let ts3 = &ts1 + &ts2;
        assert!(ts3.is_ok());

        // Check values in added TS
        let ts3 = ts3.unwrap();
        assert_eq!(ts3.values, vec![6, 8, 10, 12]);

        // Check adding TS with different timeline is not OK
        let tl2 = TimeLine::new(dr, Period::Year);
        let v4 = vec![1];
        let ts4 = TimeSeries::new(&tl2, v4).unwrap();
        let ts5 = &ts4 + &ts1;
        assert!(ts5.is_err());

        // Check adding TS with cloned timeline is OK
        let tl3 = tl.clone();
        let v6 = vec![1, 5, 8, 13];
        let ts6 = TimeSeries::new(&tl3, v6).unwrap();
        let ts7 = &ts6 + &ts1;
        assert!(ts7.is_ok());

        // Check adding negative numbers and zero
        let v8 = vec![-1, -2, 0, -100];
        let ts8 = TimeSeries::new(&tl, v8).unwrap();
        let ts9 = &ts8 + &ts2;
        assert!(ts9.is_ok());
        let ts9 = ts9.unwrap();
        assert_eq!(ts9.values, vec![4, 4, 7, -92]);

        // Check adding floats
        let v10 = vec![1.2, 1000.6, 0.0001, 3.0];
        let v11 = vec![2.8, 0.0, 4.5, -0.5];
        let ts10 = TimeSeries::new(&tl, v10).unwrap();
        let ts11 = TimeSeries::new(&tl, v11).unwrap();
        let ts12 = &ts10 + &ts11;
        assert!(ts12.is_ok());
        let ts12 = ts12.unwrap();
        assert_eq!(ts12.values, vec![4.0, 1000.6, 4.5001, 2.5]);

    }

    #[test]
    fn sub_timeseries() {
        
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = TimeLine::new(dr, Period::Quarter);

        // Create two timeseries
        let v1 = vec![1, 2, 3, 4];
        let ts1 = TimeSeries::new(&tl, v1).unwrap();
        let v2 = vec![5, 6, 7, 8];
        let ts2 = TimeSeries::new(&tl, v2).unwrap();

        // Subtract two TS and check OK
        let ts3 = &ts2 - &ts1;
        assert!(ts3.is_ok());

        // Check values in subtracted TS
        let ts3 = ts3.unwrap();
        assert_eq!(ts3.values, vec![4, 4, 4, 4]);

        // Check subtracting TS with different timeline is not OK
        let tl2 = TimeLine::new(dr, Period::Year);
        let v4 = vec![1];
        let ts4 = TimeSeries::new(&tl2, v4).unwrap();
        let ts5 = &ts4 - &ts1;
        assert!(ts5.is_err());

        // Check subracting TS with cloned timeline is OK
        let tl3 = tl.clone();
        let v6 = vec![1, 5, 8, 13];
        let ts6 = TimeSeries::new(&tl3, v6).unwrap();
        let ts7 = &ts6 - &ts1;
        assert!(ts7.is_ok());

        // Check subtracting negative numbers and zero
        let v8 = vec![-1, -2, 0, -100];
        let ts8 = TimeSeries::new(&tl, v8).unwrap();
        let ts9 = &ts8 - &ts2;
        assert!(ts9.is_ok());
        let ts9 = ts9.unwrap();
        assert_eq!(ts9.values, vec![-6, -8, -7, -108]);

        // Check subtracting floats
        let v10 = vec![1.2, 1000.6, 0.0001, 3.0];
        let v11 = vec![2.8, 0.0, 4.5, -0.5];
        let ts10 = TimeSeries::new(&tl, v10).unwrap();
        let ts11 = TimeSeries::new(&tl, v11).unwrap();
        let ts12 = &ts10 - &ts11;
        assert!(ts12.is_ok());
        let ts12 = ts12.unwrap();
        assert!((ts12.values[0] as f64 + 1.6).abs() < 1e-10);
        assert!((ts12.values[1] as f64 - 1000.6).abs() < 1e-10);
        assert!((ts12.values[2] as f64 + 4.4999).abs() < 1e-10);
        assert!((ts12.values[3] as f64 - 3.5).abs() < 1e-10);

    }

    #[test]
    fn mul_timeseries() {
        
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = TimeLine::new(dr, Period::Quarter);

        // Create two timeseries
        let v1 = vec![1, 2, 3, 4];
        let ts1 = TimeSeries::new(&tl, v1).unwrap();
        let v2 = vec![5, 6, 7, 8];
        let ts2 = TimeSeries::new(&tl, v2).unwrap();

        // Multiply two TS and check OK
        let ts3 = &ts1 * &ts2;
        assert!(ts3.is_ok());

        // Check values in multiplied TS
        let ts3 = ts3.unwrap();
        assert_eq!(ts3.values, vec![5, 12, 21, 32]);

        // Check multiplying TS with different timeline is not OK
        let tl2 = TimeLine::new(dr, Period::Year);
        let v4 = vec![1];
        let ts4 = TimeSeries::new(&tl2, v4).unwrap();
        let ts5 = &ts4 * &ts1;
        assert!(ts5.is_err());

        // Check multiplying TS with cloned timeline is OK
        let tl3 = tl.clone();
        let v6 = vec![1, 5, 8, 13];
        let ts6 = TimeSeries::new(&tl3, v6).unwrap();
        let ts7 = &ts6 * &ts1;
        assert!(ts7.is_ok());

        // Check multiplying negative numbers and zero
        let v8 = vec![-1, -2, 0, -100];
        let ts8 = TimeSeries::new(&tl, v8).unwrap();
        let ts9 = &ts8 * &ts2;
        assert!(ts9.is_ok());
        let ts9 = ts9.unwrap();
        assert_eq!(ts9.values, vec![-5, -12, 0, -800]);

        // Check multiplying floats
        let v10 = vec![1.2, 1000.6, 0.0001, 3.0];
        let v11 = vec![2.8, 0.0, 4.5, -0.5];
        let ts10 = TimeSeries::new(&tl, v10).unwrap();
        let ts11 = TimeSeries::new(&tl, v11).unwrap();
        let ts12 = &ts10 * &ts11;
        assert!(ts12.is_ok());
        let ts12 = ts12.unwrap();
        assert!((ts12.values[0] as f64 - 3.36).abs() < 1e-10);
        assert!((ts12.values[1] as f64 - 0.0).abs() < 1e-10);
        assert!((ts12.values[2] as f64 - 0.00045).abs() < 1e-10);
        assert!((ts12.values[3] as f64 + 1.5).abs() < 1e-10);

    }

    #[test]
    fn div_timeseries() {
        
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = TimeLine::new(dr, Period::Quarter);

        // Create two timeseries
        let v1 = vec![1, 2, 3, 4];
        let ts1 = TimeSeries::new(&tl, v1).unwrap();
        let v2 = vec![5, 6, 7, 8];
        let ts2 = TimeSeries::new(&tl, v2).unwrap();

        // Divide two TS and check OK
        let ts3 = &ts2 / &ts1;
        assert!(ts3.is_ok());

        // Check values in divided TS
        let ts3 = ts3.unwrap();
        assert_eq!(ts3.values, vec![5, 3, 2, 2]);

        // Check dividing TS with different timeline is not OK
        let tl2 = TimeLine::new(dr, Period::Year);
        let v4 = vec![1];
        let ts4 = TimeSeries::new(&tl2, v4).unwrap();
        let ts5 = &ts4 / &ts1;
        assert!(ts5.is_err());

        // Check dividing TS with cloned timeline is OK
        let tl3 = tl.clone();
        let v6 = vec![1, 5, 8, 13];
        let ts6 = TimeSeries::new(&tl3, v6).unwrap();
        let ts7 = &ts6 / &ts1;
        assert!(ts7.is_ok());

        // Check dividing negative numbers and zero
        let v8 = vec![-1, -2, 0, -100];
        let ts8 = TimeSeries::new(&tl, v8).unwrap();
        let ts9 = &ts8 / &ts1;
        assert!(ts9.is_ok());
        let ts9 = ts9.unwrap();
        assert_eq!(ts9.values, vec![-1, -1, 0, -25]);

        // Check dividing floats
        let v10 = vec![1.2, 1000.6, 0.0001, 3.0];
        let v11 = vec![2.8, 0.0, 4.5, -0.5];
        let ts10 = TimeSeries::new(&tl, v10).unwrap();
        let ts11 = TimeSeries::new(&tl, v11).unwrap();
        let ts12 = &ts10 / &ts11;
        assert!(ts12.is_ok());
        let ts12 = ts12.unwrap();
        assert!((ts12.values[0] as f64 - 0.428571428571).abs() < 1e-10);
        assert_eq!(ts12.values[1], f64::INFINITY);
        assert!((ts12.values[2] as f64 - 0.000022222222).abs() < 1e-10);
        assert!((ts12.values[3] as f64 + 6.0).abs() < 1e-10);

    }

    #[test]
    fn rem_timeseries() {
        
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = TimeLine::new(dr, Period::Quarter);

        // Create two timeseries
        let v1 = vec![1, 2, 3, 4];
        let ts1 = TimeSeries::new(&tl, v1).unwrap();
        let v2 = vec![5, 6, 7, 11];
        let ts2 = TimeSeries::new(&tl, v2).unwrap();

        // Mod two TS and check OK
        let ts3 = &ts2 % &ts1;
        assert!(ts3.is_ok());

        // Check values in mod TS
        let ts3 = ts3.unwrap();
        assert_eq!(ts3.values, vec![0, 0, 1, 3]);

        // Check mod TS with different timeline is not OK
        let tl2 = TimeLine::new(dr, Period::Year);
        let v4 = vec![1];
        let ts4 = TimeSeries::new(&tl2, v4).unwrap();
        let ts5 = &ts4 % &ts1;
        assert!(ts5.is_err());

        // Check mod TS with cloned timeline is OK
        let tl3 = tl.clone();
        let v6 = vec![1, 5, 8, 13];
        let ts6 = TimeSeries::new(&tl3, v6).unwrap();
        let ts7 = &ts6 % &ts1;
        assert!(ts7.is_ok());

        // Check mod negative numbers and zero
        // Not sure this is that useful, would we ever be doing this???
        let v8 = vec![-1, -2, 0, -100];
        let ts8 = TimeSeries::new(&tl, v8).unwrap();
        let ts9 = &ts8 % &ts2;
        assert!(ts9.is_ok());
        let ts9 = ts9.unwrap();
        assert_eq!(ts9.values, vec![-1, -2, 0, -1]);

        // Check mod floats
        // CBA
        /*let v10 = vec![1.2, 1000.6, 0.0001, 3.0];
        let v11 = vec![2.8, 0.0, 4.5, -0.5];
        let ts10 = TimeSeries::new(&tl, v10).unwrap();
        let ts11 = TimeSeries::new(&tl, v11).unwrap();
        let ts12 = &ts10 % &ts11;
        assert!(ts12.is_ok());
        let ts12 = ts12.unwrap();
        assert_eq!(ts12.values, vec![4.0, 1000.6, 4.5001, 2.5]);*/

    }

}