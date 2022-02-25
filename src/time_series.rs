use crate::{timeline::Timeline, DateRange};
use std::ops::{Add, AddAssign, Div, Mul, Rem, Sub};
use time::Date;

pub enum AggType {
    Add,
    ArithmeticMean,
    GeometricMean,
    LinearInterpolation,
}

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
    pub(crate) timeline: &'a Timeline,
    values: Vec<T>,
}

impl<'a, T> TimeSeries<'a, T> {
    // region: constructors

    /// Create a new TimeSeries object
    ///
    /// This method will throw an error if the length of the timeline provided and the
    /// length of the value vector do not match
    pub fn new(timeline: &'a Timeline, values: Vec<T>) -> Result<Self, &'static str> {
        match i32::try_from(values.len()) {
            Ok(l) => {
                if l != timeline.len {
                    return Err("Values do not match the timeline");
                }
            }
            Err(_) => {
                return Err("Couldn't convert length of values into i32");
            }
        }
        Ok(TimeSeries { timeline, values })
    }

    // TODO: implement other ways of creating a TS object:
    //  * just provide some values and then pad out to full timeline

    // endregion constructors

    // region: getters
    /// Return timeseries value at date
    pub fn value(&self, date: Date) -> Option<&T> {
        let i = self.timeline.index_at(date)?;
        self.values.get(i as usize)
    }

    /// Return a reference to the underlying timeseries values
    /// for the values that span the given date range. Note that
    /// the whole of the supplied date range must lie within the
    /// timeline of the `TimeSeries` or rhis will return `None`
    pub fn value_range(&self, dr: DateRange) -> Option<&[T]> {
        let start = self.timeline.index_at(dr.from())? as usize;
        let end = self.timeline.index_at(dr.to())? as usize;
        self.values.get(start..=end)
    }
    // endregion getters

    // region: change_period
    /*pub fn change_periodicity(
        &self,
        timeline: &'a Timeline,
        transform: AggType,
    ) -> Result<TimeSeries<'a, T>, &'static str> {
        if timeline.range.from() != self.timeline.range.from()
            || timeline.range.to() != self.timeline.range.to()
        {
            return Err("Cannot transform timeline as start and end dates do not match");
        }
        if timeline = self.timeline {
            return Ok(self.clone());
        }
        match transform {
            AggType::Add => {
                if timeline.periodicity > self.timeline.periodicity {
                    for (i, val) in self.values.iter().enumerate() {
                        if self.timeline.index(date)
                    }
                }
            },
            _ => {}
        }
    }*/

    /*fn add_up(&self, timeline: &'a Timeline) -> TimeSeries<'a, T>
    where
        T: AddAssign + Add<Output = T> + Copy,
    {
        let target_range = timeline.next().unwrap();
        let mut out: T;
        let mut data: Vec<T> = Vec::with_capacity(timeline.len as usize);
        for (val, range) in self.values.iter().zip(self.timeline.clone().into_iter()) {
            if target_range.fully_contains(&range) {
                out += *val;
            } else {
                if let Some(dr) = target_range.intersect(&range) {
                    // TODO: figure out how to apportion for part periods
                    //out += *val * dr.as_days() / range.as_days();
                    //nxt = *val - *val * dr.as_days() / range.as_days();
                }
                data.push(out);
                let Some(target_range) = timeline.next();
            }
        }
        TimeSeries::new(timeline, data).unwrap()
    }*/
    // endregion change_period

    // TODO: implement way to add values into an existing TS, maybe by providing a (Date, T) tuple

    // TODO: implement a way of building corkscrews with multiple operations

    // TODO: implement a shift method so that operations can be done on time series objects that reference different time periods
    //  all combination methods currently offered are strictly limited to looking across isolated time periods
    //  need to think carefully about if this will expose any circularity issues
}

// region: cast_values
impl<'a, T> TimeSeries<'a, T>
where
    T: Copy + Into<f64>,
{
    /// Change underlying data series into 64-bit float type. The source type has to
    /// be capable of beinng converted e.e. won't work on String
    pub fn cast_f64(&self) -> TimeSeries<'a, f64> {
        let mut data = Vec::with_capacity(self.values.len());
        for val in self.values.iter() {
            let v1 = *val;
            let v = v1.into();
            data.push(v);
        }
        TimeSeries::new(self.timeline, data).unwrap()
    }
}

impl<'a, T> TimeSeries<'a, T>
where
    T: Copy + Into<i32>,
{
    pub fn cast_i32(&self) -> TimeSeries<'a, i32> {
        let mut data = Vec::with_capacity(self.values.len());
        for val in self.values.iter() {
            let v1 = *val;
            let v = v1.into();
            data.push(v);
        }
        TimeSeries::new(self.timeline, data).unwrap()
    }
}
// endregion cast_values

// region: empty_constuctors
impl<'a> TimeSeries<'a, i32> {
    /// For a given timline, create a TimeSeries of 32-bit integers, all with value 0
    pub fn empty_i(timeline: &'a Timeline) -> TimeSeries<'a, i32> {
        let values = vec![0; timeline.len as usize];
        TimeSeries { timeline, values }
    }
}

impl<'a> TimeSeries<'a, f64> {
    /// For a given timline, create a TimeSeries of 64-bit floats, all with value 0
    pub fn empty_f(timeline: &'a Timeline) -> TimeSeries<'a, f64> {
        let values = vec![0.0; timeline.len as usize];
        TimeSeries { timeline, values }
    }
}
// endregion empty_constuctors

// TODO: provide a means to have a generic calc on more than a pair of TS objects
//  current implementation is strictly limited to two operations
// region: generic_func

impl<'a, T> TimeSeries<'a, T> {
    /// Allows the user to provide a closure that defines the pairwise combination
    /// of two time series
    ///
    /// Note that for simple artihmetic operations (+, -, *, /) these operators are already
    /// directly defined for the TimeSeries object, so that as long as you can apply the
    /// arithmetic operation on the underlying value type (e.g. you can't divide Strings)
    /// then you will be able to write something like this: `ts3 = &ts1 + &ts2;` or
    /// `ts3 = &ts1 + 10;`
    ///
    /// The closure cannot have side effects (i.e. change the inputs provided). This
    /// is to ensure that the `TimeSeries` being operated on, don't change in the process
    /// of generating a new `TimeSeries`
    ///
    /// ---
    /// ### Example
    /// ```
    /// use timeseries::{TimeSeries, Timeline, DateRange, Period};
    /// use time::{Date, Month};
    ///
    /// // Create a timeline
    /// let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
    /// let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
    /// let dr = DateRange::new(from, to);
    /// let tl = Timeline::new(dr, Period::Quarter);
    ///
    /// // Create two timeseries
    /// let v1 = vec![1, 2, 3, 4];
    /// let ts1 = TimeSeries::new(&tl, v1).unwrap();
    /// let v2 = vec![5, 6, 7, 8];
    /// let ts2 = TimeSeries::new(&tl, v2).unwrap();
    ///
    /// // Write a generic function that can be pairwise applied to the elements of a TS and apply it
    /// let op = |(&a, &b): (&i32, &i32)| -> i32 {
    ///     if a < 3 {
    ///         1
    ///     } else {
    ///         b + 1
    ///     }
    /// };
    /// let ts3 = ts1.apply(&ts2, op).unwrap();
    /// ```
    pub fn apply<F>(&self, other: &TimeSeries<'a, T>, func: F) -> Result<TimeSeries<'a, T>, &str>
    where
        F: FnMut((&T, &T)) -> T,
        T: Copy,
    {
        if self.timeline != other.timeline {
            return Err("Timelines do not match. Ensure a common timeline is being used");
        }
        let data = self
            .values
            .iter()
            .zip(other.values.iter())
            .map(func)
            .collect();
        // Went with unwrap here as a TimeSeries created in these conditions should always be OK
        Ok(TimeSeries::new(self.timeline, data).unwrap())
    }
}
// endregion generic_func

// TODO: implement the OpAssign traits, such as AddAssign & DivAssign
// region: arithmetic_ops

// region: arithmetic_add
// Add timeseries to timeseries
impl<'a, 'b, 'c, T> Add<&'c TimeSeries<'a, T>> for &'b TimeSeries<'a, T>
where
    T: Add + Add<Output = T> + Copy,
{
    type Output = Result<TimeSeries<'a, T>, &'static str>;

    fn add(self, rhs: &'c TimeSeries<'a, T>) -> Result<TimeSeries<'a, T>, &'static str> {
        if self.timeline != rhs.timeline {
            return Err("Timelines do not match. Ensure a common timeline is being used");
        }
        let data = self
            .values
            .iter()
            .zip(rhs.values.iter())
            .map(|(&a, &b)| a + b)
            .collect();
        // Went with unwrap here as a TimeSeries created in these conditions should always be OK
        Ok(TimeSeries::new(self.timeline, data).unwrap())
    }
}

// Add static value to timeseries
impl<'a, 'b, T> Add<T> for &'b TimeSeries<'a, T>
where
    T: Add + Add<Output = T> + Copy,
{
    type Output = TimeSeries<'a, T>;

    fn add(self, rhs: T) -> TimeSeries<'a, T> {
        let data = self.values.iter().map(|&a| a + rhs).collect();
        // Went with unwrap here as a TimeSeries created in these conditions should always be OK
        TimeSeries::new(self.timeline, data).unwrap()
    }
}
// endregion arithmetic_add

// region: arithmetic_sub
// Subtract timeseries from timeseries
impl<'a, 'b, 'c, T> Sub<&'c TimeSeries<'a, T>> for &'b TimeSeries<'a, T>
where
    T: Sub + Sub<Output = T> + Copy,
{
    type Output = Result<TimeSeries<'a, T>, &'static str>;

    fn sub(self, rhs: &'c TimeSeries<'a, T>) -> Result<TimeSeries<'a, T>, &'static str> {
        if self.timeline != rhs.timeline {
            return Err("Timelines do not match. Ensure a common timeline is being used");
        }
        let data = self
            .values
            .iter()
            .zip(rhs.values.iter())
            .map(|(&a, &b)| a - b)
            .collect();
        // Went with unwrap here as a TimeSeries created in these conditions should always be OK
        Ok(TimeSeries::new(self.timeline, data).unwrap())
    }
}

// Subtract static value from timeseries
impl<'a, 'b, T> Sub<T> for &'b TimeSeries<'a, T>
where
    T: Sub + Sub<Output = T> + Copy,
{
    type Output = TimeSeries<'a, T>;

    fn sub(self, rhs: T) -> TimeSeries<'a, T> {
        let data = self.values.iter().map(|&a| a - rhs).collect();
        // Went with unwrap here as a TimeSeries created in these conditions should always be OK
        TimeSeries::new(self.timeline, data).unwrap()
    }
}
// endregion arithmetic_sub

// region: arithmetic_mul
// Multiply one timeseries with another timeseries
impl<'a, 'b, 'c, T> Mul<&'c TimeSeries<'a, T>> for &'b TimeSeries<'a, T>
where
    T: Mul + Mul<Output = T> + Copy,
{
    type Output = Result<TimeSeries<'a, T>, &'static str>;

    fn mul(self, rhs: &'c TimeSeries<'a, T>) -> Result<TimeSeries<'a, T>, &'static str> {
        if self.timeline != rhs.timeline {
            return Err("Timelines do not match. Ensure a common timeline is being used");
        }
        let data = self
            .values
            .iter()
            .zip(rhs.values.iter())
            .map(|(&a, &b)| a * b)
            .collect();
        // Went with unwrap here as a TimeSeries created in these conditions should always be OK
        Ok(TimeSeries::new(self.timeline, data).unwrap())
    }
}

// Multiply one timeseries with a static value
impl<'a, 'b, T> Mul<T> for &'b TimeSeries<'a, T>
where
    T: Mul + Mul<Output = T> + Copy,
{
    type Output = TimeSeries<'a, T>;

    fn mul(self, rhs: T) -> TimeSeries<'a, T> {
        let data = self.values.iter().map(|&a| a * rhs).collect();
        // Went with unwrap here as a TimeSeries created in these conditions should always be OK
        TimeSeries::new(self.timeline, data).unwrap()
    }
}
// endregion arithmetic_mul

// region: arithmetic_div
// Divide one timeseries with another timeseries
impl<'a, 'b, 'c, T> Div<&'c TimeSeries<'a, T>> for &'b TimeSeries<'a, T>
where
    T: Div + Div<Output = T> + Copy,
{
    type Output = Result<TimeSeries<'a, T>, &'static str>;

    fn div(self, rhs: &'c TimeSeries<'a, T>) -> Result<TimeSeries<'a, T>, &'static str> {
        if self.timeline != rhs.timeline {
            return Err("Timelines do not match. Ensure a common timeline is being used");
        }
        let data = self
            .values
            .iter()
            .zip(rhs.values.iter())
            .map(|(&a, &b)| a / b)
            .collect();
        // Went with unwrap here as a TimeSeries created in these conditions should always be OK
        Ok(TimeSeries::new(self.timeline, data).unwrap())
    }
}

// Divide one timeseries with a static value
impl<'a, 'b, T> Div<T> for &'b TimeSeries<'a, T>
where
    T: Div + Div<Output = T> + Copy,
{
    type Output = TimeSeries<'a, T>;

    fn div(self, rhs: T) -> TimeSeries<'a, T> {
        let data = self.values.iter().map(|&a| a / rhs).collect();
        // Went with unwrap here as a TimeSeries created in these conditions should always be OK
        TimeSeries::new(self.timeline, data).unwrap()
    }
}
// endregion arithmetic_div

// region: arithmetic_rem
// Remainder of one timeseries from another timeseries
impl<'a, 'b, 'c, T> Rem<&'c TimeSeries<'a, T>> for &'b TimeSeries<'a, T>
where
    T: Rem + Rem<Output = T> + Copy,
{
    type Output = Result<TimeSeries<'a, T>, &'static str>;

    fn rem(self, rhs: &'c TimeSeries<'a, T>) -> Result<TimeSeries<'a, T>, &'static str> {
        if self.timeline != rhs.timeline {
            return Err("Timelines do not match. Ensure a common timeline is being used");
        }
        let data = self
            .values
            .iter()
            .zip(rhs.values.iter())
            .map(|(&a, &b)| a % b)
            .collect();
        // Went with unwrap here as a TimeSeries created in these conditions should always be OK
        Ok(TimeSeries::new(self.timeline, data).unwrap())
    }
}

// Remainder of one timeseries from a static value
impl<'a, 'b, T> Rem<T> for &'b TimeSeries<'a, T>
where
    T: Rem + Rem<Output = T> + Copy,
{
    type Output = TimeSeries<'a, T>;

    fn rem(self, rhs: T) -> TimeSeries<'a, T> {
        let data = self.values.iter().map(|&a| a % rhs).collect();
        // Went with unwrap here as a TimeSeries created in these conditions should always be OK
        TimeSeries::new(self.timeline, data).unwrap()
    }
}
// endregion arithmetic_rem
// endregion arithmetic_ops

#[cfg(test)]
mod tests {

    use super::*;
    use crate::{DateRange, Period};
    use time::{Date, Month};

    #[test]
    fn create_timeseries() {
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = Timeline::new(dr, Period::Quarter);

        // Create timeseries, check ok
        let v1 = vec![1, 2, 3, 4];
        let ts1 = TimeSeries::new(&tl, v1);
        assert!(ts1.is_ok());

        // Create a timeseries of Strings (why?), check they're ok too
        let v2 = vec![
            String::from("a"),
            String::from("loerm ipsum"),
            String::from("hello, World!"),
            String::from("!£$%^&*()/|jkhsdaf`"),
        ];
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
        if let Err(e) = ts3 {
            assert_eq!(e, "Values do not match the timeline")
        }

        // Create a timeseries that's longer than i32 (eek!) and check it errors out
        let len: usize = 2_147_483_648;
        let v4 = vec![0; len];

        let ts4 = TimeSeries::new(&tl, v4);
        assert!(ts4.is_err());
        if let Err(e) = ts4 {
            assert_eq!(e, "Couldn't convert length of values into i32")
        }

        // Create a timeseries that's just shorter than i32 and check it's ok
    }

    #[test]
    fn create_empty_timeseries() {
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = Timeline::new(dr, Period::Quarter);

        // Create float and integer ts, check OK
        let ts_i = TimeSeries::empty_i(&tl);
        assert_eq!(ts_i.values, vec![0, 0, 0, 0]);
        let ts_f = TimeSeries::empty_f(&tl);
        assert_eq!(ts_f.values, vec![0.0, 0.0, 0.0, 0.0]);
    }

    #[test]
    fn value() {
        // Create timeseries
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = Timeline::new(dr, Period::Quarter);
        let ts = TimeSeries::new(&tl, vec![1, 2, 3, 4]).unwrap();

        // Check first date
        let mut d = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        assert_eq!(ts.value(d), Some(&1));

        // Check date in first period
        d = Date::from_calendar_date(2022, Month::February, 28).unwrap();
        assert_eq!(ts.value(d), Some(&1));

        // Check first date in second period
        d = Date::from_calendar_date(2022, Month::April, 10).unwrap();
        assert_eq!(ts.value(d), Some(&2));

        // Check last date
        d = to.previous_day().unwrap();
        assert_eq!(ts.value(d), Some(&4));

        // Check out of bounds
        d = to;
        assert!(ts.value(d).is_none());
        d = from.previous_day().unwrap();
        assert!(ts.value(d).is_none());
    }

    #[test]
    fn value_range() {
        // Create timeseries
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = Timeline::new(dr, Period::Quarter);
        let ts = TimeSeries::new(&tl, vec![1, 2, 3, 4]).unwrap();

        // Check first date
        let mut d1 = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let mut d2 = Date::from_calendar_date(2022, Month::February, 10).unwrap();
        let mut dr1 = DateRange::new(d1, d2);
        assert_eq!(ts.value_range(dr1), Some(&[1][..]));

        // Check whole range
        d1 = from;
        d2 = dr.last_day();
        dr1 = DateRange::new(d1, d2);
        assert_eq!(ts.value_range(dr1), Some(&[1, 2, 3, 4][..]));

        // Check half range
        d1 = Date::from_calendar_date(2022, Month::August, 10).unwrap();
        d2 = dr.last_day();
        dr1 = DateRange::new(d1, d2);
        assert_eq!(ts.value_range(dr1), Some(&[3, 4][..]));

        // Check out of bounds
        d1 = Date::from_calendar_date(2022, Month::August, 10).unwrap();
        d2 = to;
        dr1 = DateRange::new(d1, d2);
        assert!(ts.value_range(dr1).is_none());

        d1 = from.previous_day().unwrap();
        d2 = dr.last_day();
        dr1 = DateRange::new(d1, d2);
        assert!(ts.value_range(dr1).is_none());
    }

    #[test]
    fn cast_f64() {
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = Timeline::new(dr, Period::Quarter);

        // Create a timeseries
        let v1 = vec![1, 2, 3, 4];
        let ts1 = TimeSeries::new(&tl, v1).unwrap();

        assert_eq!(ts1.cast_f64().values, vec![1.0, 2.0, 3.0, 4.0]);
    }

    #[test]
    fn cast_i32() {
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = Timeline::new(dr, Period::Quarter);

        // Create a timeseries
        let v1 = vec![true, true, false, true];
        let ts1 = TimeSeries::new(&tl, v1).unwrap();

        assert_eq!(ts1.cast_i32().values, vec![1, 1, 0, 1]);
    }

    #[test]
    fn gen_func_timeseries() {
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = Timeline::new(dr, Period::Quarter);

        // Create two timeseries
        let v1 = vec![1, 2, 3, 4];
        let ts1 = TimeSeries::new(&tl, v1).unwrap();
        let v2 = vec![5, 6, 7, 8];
        let ts2 = TimeSeries::new(&tl, v2).unwrap();

        // Write a generic function that can be pairwise applied to the elements of a TS and check OK
        let op = |(&a, &b): (&i32, &i32)| -> i32 {
            if a < 3 {
                1
            } else {
                b + 1
            }
        };
        let ts3 = ts1.apply(&ts2, op);
        assert!(ts3.is_ok());

        // Check values in added TS
        let ts3 = ts3.unwrap();
        assert_eq!(ts3.values, vec![1, 1, 8, 9]);

        // Check adding TS with different timeline is not OK
        let tl2 = Timeline::new(dr, Period::Year);
        let v4 = vec![1];
        let ts4 = TimeSeries::new(&tl2, v4).unwrap();
        let ts5 = ts4.apply(&ts1, op);
        assert!(ts5.is_err());

        // Check adding TS with cloned timeline is OK
        let tl3 = tl;
        let v6 = vec![1, 5, 8, 13];
        let ts6 = TimeSeries::new(&tl3, v6).unwrap();
        let ts7 = ts1.apply(&ts6, op);
        assert!(ts7.is_ok());

        // Check adding negative numbers and zero
        let v8 = vec![-1, -2, 0, -100];
        let ts8 = TimeSeries::new(&tl, v8).unwrap();
        let ts9 = ts1.apply(&ts8, op);
        assert!(ts9.is_ok());
        let ts9 = ts9.unwrap();
        assert_eq!(ts9.values, vec![1, 1, 1, -99]);

        // Check adding floats
        let v10 = vec![1.2, 1000.6, 0.0001, 3.0];
        let v11 = vec![2.8, 0.0, 4.5, -0.5];
        let op2 = |(&a, &b): (&f64, &f64)| -> f64 {
            if a < 3.0 {
                1.0
            } else {
                b + 1.0
            }
        };
        let ts10 = TimeSeries::new(&tl, v10).unwrap();
        let ts11 = TimeSeries::new(&tl, v11).unwrap();
        let ts12 = ts10.apply(&ts11, op2);
        assert!(ts12.is_ok());
        let ts12 = ts12.unwrap();
        assert_eq!(ts12.values, vec![1.0, 1.0, 1.0, 0.5]);
    }

    #[test]
    fn add_timeseries() {
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = Timeline::new(dr, Period::Quarter);

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
        let tl2 = Timeline::new(dr, Period::Year);
        let v4 = vec![1];
        let ts4 = TimeSeries::new(&tl2, v4).unwrap();
        let ts5 = &ts4 + &ts1;
        assert!(ts5.is_err());

        // Check adding TS with cloned timeline is OK
        let tl3 = tl;
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
    fn add_static() {
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = Timeline::new(dr, Period::Quarter);

        // Create two timeseries
        let v1 = vec![1, 2, 3, 4];
        let ts1 = TimeSeries::new(&tl, v1).unwrap();

        // Add two TS and check OK
        let ts3 = &ts1 + 5;
        assert_eq!(ts3.values, vec![6, 7, 8, 9]);

        // Check adding negative numbers and zero
        let v8 = vec![-1, -2, 0, -100];
        let ts8 = TimeSeries::new(&tl, v8).unwrap();
        let ts9 = &ts8 + 10;
        assert_eq!(ts9.values, vec![9, 8, 10, -90]);

        // Check adding floats
        let v10 = vec![1.2, 1000.6, 0.0001, 3.0];
        let ts10 = TimeSeries::new(&tl, v10).unwrap();
        let ts12 = &ts10 + 1.0;
        assert_eq!(ts12.values, vec![2.2, 1001.6, 1.0001, 4.0]);
    }

    #[test]
    fn sub_timeseries() {
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = Timeline::new(dr, Period::Quarter);

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
        let tl2 = Timeline::new(dr, Period::Year);
        let v4 = vec![1];
        let ts4 = TimeSeries::new(&tl2, v4).unwrap();
        let ts5 = &ts4 - &ts1;
        assert!(ts5.is_err());

        // Check subracting TS with cloned timeline is OK
        let tl3 = tl;
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
    fn sub_static() {
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = Timeline::new(dr, Period::Quarter);

        // Create timeseries
        let v1 = vec![1, 2, 3, 4];
        let ts1 = TimeSeries::new(&tl, v1).unwrap();

        // Subtract and check answers
        let ts3 = &ts1 - 1;
        assert_eq!(ts3.values, vec![0, 1, 2, 3]);

        // Check subtracting negative numbers and zero
        let v8 = vec![-1, -2, 0, -100];
        let ts8 = TimeSeries::new(&tl, v8).unwrap();
        let ts9 = &ts8 - 10;
        assert_eq!(ts9.values, vec![-11, -12, -10, -110]);

        // Check subtracting floats
        let v10 = vec![1.2, 1000.6, 0.0001, 3.0];
        let ts10 = TimeSeries::new(&tl, v10).unwrap();
        let ts12 = &ts10 - 1.0;
        assert!((ts12.values[0] as f64 - 0.2).abs() < 1e-10);
        assert!((ts12.values[1] as f64 - 999.6).abs() < 1e-10);
        assert!((ts12.values[2] as f64 + 0.9999).abs() < 1e-10);
        assert!((ts12.values[3] as f64 - 2.0).abs() < 1e-10);
    }

    #[test]
    fn mul_timeseries() {
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = Timeline::new(dr, Period::Quarter);

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
        let tl2 = Timeline::new(dr, Period::Year);
        let v4 = vec![1];
        let ts4 = TimeSeries::new(&tl2, v4).unwrap();
        let ts5 = &ts4 * &ts1;
        assert!(ts5.is_err());

        // Check multiplying TS with cloned timeline is OK
        let tl3 = tl;
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
    fn mul_static() {
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = Timeline::new(dr, Period::Quarter);

        // Create two timeseries
        let v1 = vec![1, 2, 3, 4];
        let ts1 = TimeSeries::new(&tl, v1).unwrap();

        // Multiply two TS and check OK
        let ts3 = &ts1 * 2;
        assert_eq!(ts3.values, vec![2, 4, 6, 8]);

        // Check multiplying negative numbers and zero
        let v8 = vec![-1, -2, 0, -100];
        let ts8 = TimeSeries::new(&tl, v8).unwrap();
        let ts9 = &ts8 * 2;
        assert_eq!(ts9.values, vec![-2, -4, 0, -200]);

        // Check multiplying floats
        let v10 = vec![1.2, 1000.6, 0.0001, 3.0];
        let ts10 = TimeSeries::new(&tl, v10).unwrap();
        let ts12 = &ts10 * 2.0;
        assert!((ts12.values[0] as f64 - 2.4).abs() < 1e-10);
        assert!((ts12.values[1] as f64 - 2001.2).abs() < 1e-10);
        assert!((ts12.values[2] as f64 - 0.0002).abs() < 1e-10);
        assert!((ts12.values[3] as f64 - 6.0).abs() < 1e-10);
    }

    #[test]
    fn div_timeseries() {
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = Timeline::new(dr, Period::Quarter);

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
        let tl2 = Timeline::new(dr, Period::Year);
        let v4 = vec![1];
        let ts4 = TimeSeries::new(&tl2, v4).unwrap();
        let ts5 = &ts4 / &ts1;
        assert!(ts5.is_err());

        // Check dividing TS with cloned timeline is OK
        let tl3 = tl;
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
    fn div_static() {
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = Timeline::new(dr, Period::Quarter);

        // Create two timeseries
        let v1 = vec![1, 2, 3, 4];
        let ts1 = TimeSeries::new(&tl, v1).unwrap();
        let ts3 = &ts1 / 2;
        assert_eq!(ts3.values, vec![0, 1, 1, 2]);

        // Check dividing negative numbers and zero
        let v8 = vec![-1, -2, 0, -100];
        let ts8 = TimeSeries::new(&tl, v8).unwrap();
        let ts9 = &ts8 / 2;
        assert_eq!(ts9.values, vec![0, -1, 0, -50]);

        // Check dividing floats
        let v10 = vec![1.2, 1000.6, 0.0001, 3.0];
        let ts10 = TimeSeries::new(&tl, v10).unwrap();
        let ts12 = &ts10 / 2.0;
        assert!((ts12.values[0] as f64 - 0.6).abs() < 1e-10);
        assert!((ts12.values[1] as f64 - 500.3).abs() < 1e-10);
        assert!((ts12.values[2] as f64 - 0.00005).abs() < 1e-10);
        assert!((ts12.values[3] as f64 - 1.5).abs() < 1e-10);
    }

    #[test]
    fn rem_timeseries() {
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = Timeline::new(dr, Period::Quarter);

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
        let tl2 = Timeline::new(dr, Period::Year);
        let v4 = vec![1];
        let ts4 = TimeSeries::new(&tl2, v4).unwrap();
        let ts5 = &ts4 % &ts1;
        assert!(ts5.is_err());

        // Check mod TS with cloned timeline is OK
        let tl3 = tl;
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

    #[test]
    fn rem_static() {
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = Timeline::new(dr, Period::Quarter);

        // Create two timeseries
        let v1 = vec![1, 2, 3, 4];
        let ts1 = TimeSeries::new(&tl, v1).unwrap();
        let ts3 = &ts1 % 2;
        assert_eq!(ts3.values, vec![1, 0, 1, 0]);

        // Check mod negative numbers and zero
        // Not sure this is that useful, would we ever be doing this???
        let v8 = vec![-1, -2, 0, -100];
        let ts8 = TimeSeries::new(&tl, v8).unwrap();
        let ts9 = &ts8 % 2;
        assert_eq!(ts9.values, vec![-1, 0, 0, 0]);

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
