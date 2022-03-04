use crate::{DateRange, Duration, Period, TimeSeriesError, Timeline};
use std::cmp;
use std::ops::{Add, Div, Mul, Rem, Sub};
use time::Date;

pub enum AggType {
    Add,
    Mean,
    Linear,
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
/// on references to TimeSeries only. This is required as TimeSeries cannot implement
/// the `Copy` trait, due it's wrapping of a vector, which does not implement the
/// `Copy` trait. Without the `Copy` trait, all the arithmetic operations, and in fact
/// any function call, move the operands. This would mean that after `let c = a + b;`
/// both `a` and `b` would no longer be available. Instead the only implemented operations
/// are on references, so `let c = &a + &b;`, which allows `a` and `b` to persist beyond
/// the addition call
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TimeSeries<'a, T> {
    timeline: &'a Timeline,
    values: Vec<T>,
}

impl<'a, T> TimeSeries<'a, T>
where
    T: Clone,
{
    // region: constructors

    /// Internal method to create a new TimeSeries object
    ///
    /// Does not check that the  timeline and the values match in
    /// length. This is a fundamental requirement for TimeSeries
    /// objects to be well formed, so restricting this to be an internal
    /// method only
    fn new_unchecked(timeline: &'a Timeline, values: Vec<T>) -> Self {
        TimeSeries { timeline, values }
    }

    /// Create a new TimeSeries object
    ///
    /// This method will throw an error if the length of the timeline provided and the
    /// length of the value vector do not match
    pub fn new(timeline: &'a Timeline, values: Vec<T>) -> Result<Self, TimeSeriesError> {
        if values.len() != timeline.len {
            return Err(TimeSeriesError::TimelineDoesNotMatchValues);
        }
        Ok(TimeSeries::new_unchecked(timeline, values))
    }

    /// Create a new TimeSeries object with a partial
    /// specification of the input values. The method will
    /// pad out values either side of the provided values to
    /// ensure that the TimeSeries is properly formed.
    ///
    /// If the values, after the start offset, do not fit within
    /// the timeline the rightmost values will be silently discarded.
    /// In extremis, if the start index provided is greater than the
    /// timeline, then the returned TimeSeries will only contain the
    /// pad values and none of the values vector will remain
    pub fn new_partial(timeline: &'a Timeline, start: usize, values: Vec<T>, pad: T) -> Self {
        let mut data;
        // If start is after the timeline then just return a vector full of the pad value
        if start >= timeline.len {
            data = vec![pad; timeline.len];
            return TimeSeries::new_unchecked(timeline, data);
        }
        // Pad before the start
        let p = pad.clone();
        data = vec![p; start];
        // Add the values
        let val_len = cmp::min(values.len(), timeline.len - start);
        data.extend_from_slice(&values[..val_len]);
        // Pad to the end as required
        let mut end = vec![pad; timeline.len - start - val_len];
        data.append(&mut end);
        // ... and out
        TimeSeries::new_unchecked(timeline, data)
    }

    // endregion constructors

    // region: shift

    /// Shift the TimeSeries by a fixed duration. Intened to use values in
    /// different periods e.g. operate on value from 6 months ago.
    ///
    /// This operation will be lossy in the sense that some values will be
    /// shifted off the end of the timeline, and will get discarded. On the
    /// other side, new values will be brought into scope, which is what the
    /// pad value is required for
    pub fn shift(&self, shift: Duration, pad: T) -> Result<Self, TimeSeriesError> {
        let shift_len = match self.timeline.periodicity {
            Period::Year => {
                if shift.days() > 0 || shift.months() > 0 {
                    return Err(TimeSeriesError::BadShift(Period::Year));
                }
                match shift.years() {
                    l if l < 0 => cmp::min(-l as usize, self.values.len()),
                    l if l > 0 => cmp::min(l as usize, self.values.len()),
                    _ => 0,
                }
            }
            Period::Quarter => {
                if shift.days() > 0 || shift.months() % 3 > 0 {
                    return Err(TimeSeriesError::BadShift(Period::Year));
                }
                match shift.years() * 4 + shift.months() / 3 {
                    l if l < 0 => cmp::min(-l as usize, self.values.len()),
                    l if l > 0 => cmp::min(l as usize, self.values.len()),
                    _ => 0,
                }
            }
            Period::Month => {
                if shift.days() > 0 {
                    return Err(TimeSeriesError::BadShift(Period::Year));
                }
                match shift.years() * 12 + shift.months() {
                    l if l < 0 => cmp::min(-l as usize, self.values.len()),
                    l if l > 0 => cmp::min(l as usize, self.values.len()),
                    _ => 0,
                }
            }
            Period::Week => {
                if shift.years() > 0 || shift.months() > 0 || shift.days() % 7 > 0 {
                    return Err(TimeSeriesError::BadShift(Period::Year));
                }
                match shift.days() / 7 {
                    l if l < 0 => cmp::min(-l as usize, self.values.len()),
                    l if l > 0 => cmp::min(l as usize, self.values.len()),
                    _ => 0,
                }
            }
            Period::Day => {
                if shift.years() > 0 || shift.months() > 0 {
                    return Err(TimeSeriesError::BadShift(Period::Year));
                }
                match shift.days() {
                    l if l < 0 => cmp::min(-l as usize, self.values.len()),
                    l if l > 0 => cmp::min(l as usize, self.values.len()),
                    _ => 0,
                }
            }
        };
        let mut data = Vec::with_capacity(self.values.len());
        let data_range = self.values.len() - shift_len;
        let mut pad = vec![pad; shift_len];
        if shift.forwards() {
            data.extend_from_slice(&self.values[shift_len..]);
            data.append(&mut pad);
        } else {
            data.append(&mut pad);
            data.extend_from_slice(&self.values[..data_range]);
        }
        let ts = Self::new(self.timeline, data)?;
        Ok(ts)
    }

    // endregion shift

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
        let end = self.timeline.index_at(dr.last_day())? as usize;
        self.values.get(start..=end)
    }
    // endregion getters
}

// region: change_periodicity
// TODO: can we do this for other types as well?
impl<'a> TimeSeries<'a, f64> {
    pub fn change_periodicity(
        &self,
        timeline: &'a Timeline,
        transform: AggType,
    ) -> Result<Self, TimeSeriesError> {
        if timeline.range != self.timeline.range {
            return Err(TimeSeriesError::TimelinesDoNotMatch);
        }
        if timeline == self.timeline {
            return Ok(self.clone());
        }
        match transform {
            AggType::Add => {
                if timeline.periodicity > self.timeline.periodicity {
                    Ok(self.add_up(timeline))
                } else {
                    Ok(self.add_down(timeline))
                }
            }
            _ => Err(TimeSeriesError::AggregationTypeNotImplemented),
        }
    }

    /// Internal method to change the periodicity of a TimeSeries object
    /// from a smaller time period to a bigger one, i.e. weeks to quarters
    /// using addition as the aggregation method
    fn add_up(&self, target_timeline: &'a Timeline) -> Self {
        let source_iter = self.timeline.into_iter();
        let mut target_iter = target_timeline.into_iter();
        let mut target_day = target_iter.next().unwrap_or(target_timeline.range).to;
        let mut data: Vec<f64> = Vec::with_capacity(target_timeline.len);
        let mut val = 0.0; // Initialising to avoid a compiler warning but not actually needed
        let mut start_period = true;

        //  loop through every source period
        for (source_range, source_val) in source_iter.zip(self.values.iter()) {
            if source_range.to <= target_day {
                // If source fully within target no need to part split periods
                if start_period {
                    start_period = false;
                    val = *source_val;
                } else {
                    val += source_val;
                }
                // If we've got to the end of the target range then
                // push in the aggregated value & move on
                if source_range.to == target_day {
                    // Append the data
                    data.push(val);
                    // Set vals to start the next target period
                    start_period = true;
                    target_day = target_iter.next().unwrap_or(target_timeline.range).to;
                }
            } else {
                // Source partially beyond the target period
                // allocate part of the source to the target period and the rest to the
                // next target period
                // split done by day count
                let res = source_val
                    * f64::from(DateRange::new(source_range.from, target_day).as_days())
                    / f64::from(source_range.as_days());
                val += res;
                data.push(val);
                start_period = false; // Needed?
                val = source_val - res;
                target_day = target_iter.next().unwrap_or(target_timeline.range).to;
            }
        }
        TimeSeries::new_unchecked(target_timeline, data)
    }

    /// Internal method to change the periodicity of a TimeSeries object
    /// from a bigger time period to a smaller one, i.e. years to months
    /// using addition as the aggregation method. Since we're increasing
    /// the number of time periods it will be inferred that the target
    /// time series values will all be the same for each source period (i.e
    /// we'll divide the source values by the number target periods). There
    /// are potentially other ways to do this
    fn add_down(&self, target_timeline: &'a Timeline) -> Self {
        let source_iter = self.timeline.into_iter();
        let mut target_iter = target_timeline.into_iter();
        let mut target_day = target_timeline.range.from();
        let mut data: Vec<f64> = Vec::with_capacity(target_timeline.len);
        let mut res_end = 0.0;
        let mut res_start = 0.0;
        let mut part_end = false;
        let mut part_start = false;
        let mut val_end = 0.0;

        // TODO: This still treats the final target period as fully fitting within the source period
        // Only affects weeks but there's the possibility that the final period is a wekk of only 2
        // days and ideally this period would only hold 2/7 of the value from the period that preceeds it
        for (source_range, source_val) in source_iter.zip(self.values.iter()) {
            // Count through the target ranges until we have spanned the current source range
            let mut i = 0;
            let source_day = source_range.to;
            while target_day < source_day {
                let target_range = target_iter.next().unwrap_or(target_timeline.range);
                target_day = target_range.to;
                if target_day <= source_day {
                    i += 1;
                } else {
                    res_end = match target_range.intersect(&source_range) {
                        Some(r) => f64::from(r.as_days()) / f64::from(target_range.as_days()),
                        None => 0.0,
                    };
                    part_end = true;
                }
            }
            let val = source_val / (i as f64 + res_start + res_end);
            if part_start {
                data.push(val_end + val * res_start);
            }
            let mut vals = vec![val; i];
            data.append(&mut vals);
            part_start = part_end;
            if part_end {
                val_end = val * res_end;
                res_start = 1.0 - res_end;
                res_end = 0.0;
            }
        }
        TimeSeries::new_unchecked(target_timeline, data)
    }
}
// endregion change_periodicity

// region: update
impl<'a, T> TimeSeries<'a, T> {
    /// Update the `TimeSeries` in place. Will over-write the value at the
    /// date with the supplied value. Use `.update_add()` if you want to add the
    /// new value to the current value at the date
    pub fn update(&mut self, new_val: (Date, T)) {
        if let Some(idx) = self.timeline.index_at(new_val.0) {
            self.values[idx] = new_val.1;
        };
    }
}

impl<'a, T> TimeSeries<'a, T>
where
    T: Add + Add<Output = T> + Copy,
{
    /// Update the `TimeSeries` in place. Will add the supplied value to
    /// the value already at the date
    pub fn update_add(&mut self, new_val: (Date, T)) {
        if let Some(idx) = self.timeline.index_at(new_val.0) {
            self.values[idx] = self.values[idx] + new_val.1;
        };
    }
}
// endregion update

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
            let v = *val;
            data.push(v.into());
        }
        TimeSeries::new_unchecked(self.timeline, data)
    }
}

impl<'a, T> TimeSeries<'a, T>
where
    T: Copy + Into<i32>,
{
    pub fn cast_i32(&self) -> TimeSeries<'a, i32> {
        let mut data = Vec::with_capacity(self.values.len());
        for val in self.values.iter() {
            let v = *val;
            data.push(v.into());
        }
        TimeSeries::new_unchecked(self.timeline, data)
    }
}
// endregion cast_values

// region: empty_constuctors
impl<'a> TimeSeries<'a, i32> {
    /// For a given timline, create a TimeSeries of 32-bit integers, all with value 0
    pub fn empty_i(timeline: &'a Timeline) -> TimeSeries<'a, i32> {
        let values = vec![0; timeline.len];
        TimeSeries::new_unchecked(timeline, values)
    }
}

impl<'a> TimeSeries<'a, f64> {
    /// For a given timline, create a TimeSeries of 64-bit floats, all with value 0
    pub fn empty_f(timeline: &'a Timeline) -> TimeSeries<'a, f64> {
        let values = vec![0.0; timeline.len];
        TimeSeries::new_unchecked(timeline, values)
    }
}
// endregion empty_constuctors

// TODO: implement a way of building corkscrews with multiple operations
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
    /// use timeseries::{TimeSeries, Timeline, DateRange, Period, Duration};
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
    /// assert_eq!(ts3.value_range(dr).unwrap(), vec![1, 1, 8, 9]);
    ///
    /// ```
    pub fn apply<F>(
        &self,
        other: &TimeSeries<'a, T>,
        func: F,
    ) -> Result<TimeSeries<'a, T>, TimeSeriesError>
    where
        F: FnMut((&T, &T)) -> T,
        T: Copy,
    {
        if self.timeline != other.timeline {
            return Err(TimeSeriesError::TimelinesDoNotMatch);
        }
        let data = self
            .values
            .iter()
            .zip(other.values.iter())
            .map(func)
            .collect();
        let ts = TimeSeries::new(self.timeline, data)?;
        Ok(ts)
    }

    /// Allows the user to provide a closure that defines the pairwise combination
    /// of two time series, plus their timeline
    ///
    /// The closure cannot have side effects (i.e. change the inputs provided). This
    /// is to ensure that the `TimeSeries` being operated on, don't change in the process
    /// of generating a new `TimeSeries`
    ///
    /// ---
    /// ### Example
    /// ```
    /// use timeseries::{TimeSeries, Timeline, DateRange, Period, Duration};
    /// use time::{Date, Month};
    ///
    /// // Create a timeline
    /// let from = Date::from_calendar_date(2022, Month::January, 1).unwrap();
    /// let dur = Duration::new(0, 0, 2);
    /// let dr = DateRange::from_duration(from, dur).unwrap();
    /// let tl = Timeline::new(dr, Period::Quarter);
    ///
    /// // Create two timeseries
    /// let v1 = vec![1, 2, 3, 4, 1, 2, 3, 4];
    /// let ts1 = TimeSeries::new(&tl, v1).unwrap();
    /// let v2 = vec![5, 6, 7, 8, 9, 10, 11, 12];
    /// let ts2 = TimeSeries::new(&tl, v2).unwrap();
    ///
    /// // Create a date
    /// let date = (from + Duration::new(0, 4, 1)).unwrap().primary();
    /// // Write a generic function that can be pairwise applied to the elements of a TS and check OK
    /// let op = |(t, &a, &b): (DateRange, &i32, &i32)| -> i32 {
    ///     if t.contains(date) {
    ///         1000
    ///     } else if a < 3 {
    ///         1
    ///     } else {
    ///         b + 1
    ///     }
    /// };
    /// let ts3 = ts1.apply_with_time(&ts2, op).unwrap();
    /// assert_eq!(ts3.value_range(dr).unwrap(), vec![1, 1, 8, 9, 1, 1000, 12, 13]);
    ///
    /// ```
    pub fn apply_with_time<F>(
        &self,
        other: &TimeSeries<'a, T>,
        func: F,
    ) -> Result<TimeSeries<'a, T>, TimeSeriesError>
    where
        F: FnMut((DateRange, &T, &T)) -> T,
        T: Copy,
    {
        if self.timeline != other.timeline {
            return Err(TimeSeriesError::TimelinesDoNotMatch);
        }
        let tl = *self.timeline;
        let data = tl
            .into_iter()
            .zip(self.values.iter())
            .zip(other.values.iter())
            .map(|((a, b), c)| (a, b, c))
            .map(func)
            .collect();
        let ts = TimeSeries::new(self.timeline, data)?;
        Ok(ts)
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
    type Output = Result<TimeSeries<'a, T>, TimeSeriesError>;

    fn add(self, rhs: &'c TimeSeries<'a, T>) -> Result<TimeSeries<'a, T>, TimeSeriesError> {
        if self.timeline != rhs.timeline {
            return Err(TimeSeriesError::TimelinesDoNotMatch);
        }
        let data = self
            .values
            .iter()
            .zip(rhs.values.iter())
            .map(|(&a, &b)| a + b)
            .collect();
        let ts = TimeSeries::new(self.timeline, data)?;
        Ok(ts)
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
        TimeSeries::new_unchecked(self.timeline, data)
    }
}
// endregion arithmetic_add

// region: arithmetic_sub
// Subtract timeseries from timeseries
impl<'a, 'b, 'c, T> Sub<&'c TimeSeries<'a, T>> for &'b TimeSeries<'a, T>
where
    T: Sub + Sub<Output = T> + Copy,
{
    type Output = Result<TimeSeries<'a, T>, TimeSeriesError>;

    fn sub(self, rhs: &'c TimeSeries<'a, T>) -> Result<TimeSeries<'a, T>, TimeSeriesError> {
        if self.timeline != rhs.timeline {
            return Err(TimeSeriesError::TimelinesDoNotMatch);
        }
        let data = self
            .values
            .iter()
            .zip(rhs.values.iter())
            .map(|(&a, &b)| a - b)
            .collect();
        let ts = TimeSeries::new(self.timeline, data)?;
        Ok(ts)
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
        TimeSeries::new_unchecked(self.timeline, data)
    }
}
// endregion arithmetic_sub

// region: arithmetic_mul
// Multiply one timeseries with another timeseries
impl<'a, 'b, 'c, T> Mul<&'c TimeSeries<'a, T>> for &'b TimeSeries<'a, T>
where
    T: Mul + Mul<Output = T> + Copy,
{
    type Output = Result<TimeSeries<'a, T>, TimeSeriesError>;

    fn mul(self, rhs: &'c TimeSeries<'a, T>) -> Result<TimeSeries<'a, T>, TimeSeriesError> {
        if self.timeline != rhs.timeline {
            return Err(TimeSeriesError::TimelinesDoNotMatch);
        }
        let data = self
            .values
            .iter()
            .zip(rhs.values.iter())
            .map(|(&a, &b)| a * b)
            .collect();
        let ts = TimeSeries::new(self.timeline, data)?;
        Ok(ts)
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
        TimeSeries::new_unchecked(self.timeline, data)
    }
}
// endregion arithmetic_mul

// region: arithmetic_div
// Divide one timeseries with another timeseries
impl<'a, 'b, 'c, T> Div<&'c TimeSeries<'a, T>> for &'b TimeSeries<'a, T>
where
    T: Div + Div<Output = T> + Copy,
{
    type Output = Result<TimeSeries<'a, T>, TimeSeriesError>;

    fn div(self, rhs: &'c TimeSeries<'a, T>) -> Result<TimeSeries<'a, T>, TimeSeriesError> {
        if self.timeline != rhs.timeline {
            return Err(TimeSeriesError::TimelinesDoNotMatch);
        }
        let data = self
            .values
            .iter()
            .zip(rhs.values.iter())
            .map(|(&a, &b)| a / b)
            .collect();
        let ts = TimeSeries::new(self.timeline, data)?;
        Ok(ts)
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
        TimeSeries::new_unchecked(self.timeline, data)
    }
}
// endregion arithmetic_div

// region: arithmetic_rem
// Remainder of one timeseries from another timeseries
impl<'a, 'b, 'c, T> Rem<&'c TimeSeries<'a, T>> for &'b TimeSeries<'a, T>
where
    T: Rem + Rem<Output = T> + Copy,
{
    type Output = Result<TimeSeries<'a, T>, TimeSeriesError>;

    fn rem(self, rhs: &'c TimeSeries<'a, T>) -> Result<TimeSeries<'a, T>, TimeSeriesError> {
        if self.timeline != rhs.timeline {
            return Err(TimeSeriesError::TimelinesDoNotMatch);
        }
        let data = self
            .values
            .iter()
            .zip(rhs.values.iter())
            .map(|(&a, &b)| a % b)
            .collect();
        let ts = TimeSeries::new(self.timeline, data)?;
        Ok(ts)
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
        TimeSeries::new_unchecked(self.timeline, data)
    }
}
// endregion arithmetic_rem
// endregion arithmetic_ops

// region: iterator
impl<'a, 'b, T> IntoIterator for &'b TimeSeries<'a, T>
where
    T: 'b,
{
    type Item = (DateRange, &'b T);
    type IntoIter = TimeSeriesIterator<'a, 'b, T>;

    fn into_iter(self) -> Self::IntoIter {
        TimeSeriesIterator {
            timeline: self.timeline,
            values: &self.values[..],
            index: 0,
        }
    }
}

pub struct TimeSeriesIterator<'a, 'b, T> {
    timeline: &'a Timeline,
    values: &'b [T],
    index: usize,
}

impl<'a, 'b, T> Iterator for TimeSeriesIterator<'a, 'b, T> {
    type Item = (DateRange, &'b T);

    fn next(&mut self) -> Option<Self::Item> {
        let dr = self.timeline.index(self.index as i32)?;
        let val = self.values.get(self.index)?;
        self.index += 1;
        Some((dr, val))
    }
}
// endregion iterator

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
            assert_eq!(e, TimeSeriesError::TimelineDoesNotMatchValues);
        }
    }

    #[test]
    fn create_partial_timeseries() {
        let from = Date::from_calendar_date(2022, Month::January, 1).unwrap();
        let dur = Duration::new(0, 0, 1);
        let dr = DateRange::from_duration(from, dur).unwrap();
        let tl = Timeline::new(dr, Period::Month);

        // Begining
        let mut v = vec![1, 2, 3, 4];
        let mut ts = TimeSeries::new_partial(&tl, 0, v, 0);
        assert_eq!(ts.values, vec![1, 2, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0]);

        // Middle
        v = vec![1, 2, 3, 4];
        ts = TimeSeries::new_partial(&tl, 3, v, 0);
        assert_eq!(ts.values, vec![0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 0, 0]);

        // Part-overflow at end
        v = vec![1, 2, 3, 4];
        ts = TimeSeries::new_partial(&tl, 10, v, 0);
        assert_eq!(ts.values, vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2]);

        // Total Overflow
        v = vec![1, 2, 3, 4];
        ts = TimeSeries::new_partial(&tl, 12, v, 0);
        assert_eq!(ts.values, vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
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
        d2 = to.next_day().unwrap();
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
    fn change_periodicity_error() {
        // Create a date range
        let from = Date::from_calendar_date(2022, Month::January, 1).unwrap();
        let dur = Duration::new(0, 0, 2);
        let dr = DateRange::from_duration(from, dur).unwrap();

        // Create a timeseries
        let tl1 = Timeline::new(dr, Period::Quarter);
        let v = vec![1, 2, 3, 4, 5, 6, 7, 8];
        let ts1 = TimeSeries::new(&tl1, v).unwrap().cast_f64();

        // Create a differnt daterange
        let dr2 = DateRange::new(from, dr.last_day());
        let tl2 = Timeline::new(dr2, Period::Month);

        // Test a different date range errors
        let mut tse = ts1.change_periodicity(&tl2, AggType::Add);
        assert!(tse.is_err());

        // Test same timeline just clones
        let tl3 = Timeline::new(dr, Period::Quarter);
        let mut ts4 = ts1.change_periodicity(&tl3, AggType::Add).unwrap();
        assert_eq!(ts4.values, ts1.values);
        ts4.update((from, 100.0));
        assert_ne!(ts4.values, ts1.values);

        // Test with not implemented aggreation types
        let tl4 = Timeline::new(dr, Period::Month);
        tse = ts1.change_periodicity(&tl4, AggType::Mean);
        assert!(tse.is_err());
        tse = ts1.change_periodicity(&tl4, AggType::Linear);
        assert!(tse.is_err());
    }

    #[test]
    fn change_periodicity_add_up_f64() {
        // Create a date range
        let from = Date::from_calendar_date(2022, Month::January, 1).unwrap();
        let dur = Duration::new(0, 0, 2);
        let dr = DateRange::from_duration(from, dur).unwrap();

        // Create timelines to resize to
        let tly = Timeline::new(dr, Period::Year);
        let tlq = Timeline::new(dr, Period::Quarter);
        let tlm = Timeline::new(dr, Period::Month);
        let tlw = Timeline::new(dr, Period::Week);

        // Create a quarterly timeseries
        let tl1 = Timeline::new(dr, Period::Quarter);
        let mut v = vec![1, 2, 3, 4, 5, 6, 7, 8];
        let mut ts1 = TimeSeries::new(&tl1, v).unwrap().cast_f64();

        // Test quarters to years
        let mut ts2 = ts1.change_periodicity(&tly, AggType::Add).unwrap();
        assert_eq!(ts2.values, vec![10.0, 26.0]);

        // Create a monthly timeseries
        let tl2 = Timeline::new(dr, Period::Month);
        v = vec![
            1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
        ];
        ts1 = TimeSeries::new(&tl2, v).unwrap().cast_f64();

        // Test months to years
        ts2 = ts1.change_periodicity(&tly, AggType::Add).unwrap();
        assert_eq!(ts2.values, vec![78.0, 222.0]);

        // Test months to quarters
        ts2 = ts1.change_periodicity(&tlq, AggType::Add).unwrap();
        assert_eq!(
            ts2.values,
            vec![6.0, 15.0, 24.0, 33.0, 42.0, 51.0, 60.0, 69.0]
        );

        // Create a weekly timeseries
        let tl3 = Timeline::new(dr, Period::Week);
        v = Vec::new();
        for i in 0..105 {
            v.push(i);
        }
        ts1 = TimeSeries::new(&tl3, v).unwrap().cast_f64();

        // Test weeks to years
        ts2 = ts1.change_periodicity(&tly, AggType::Add).unwrap();
        assert!((ts2.values[0] - 1333.428571).abs() < 1e-5);
        assert!((ts2.values[1] - 4126.571429).abs() < 1e-5);

        // Test weeks to quarters
        ts2 = ts1.change_periodicity(&tlq, AggType::Add).unwrap();
        assert!((ts2.values[0] - 76.28571429).abs() < 1e-5);
        assert!((ts2.values[1] - 245.1428571).abs() < 1e-5);
        assert!((ts2.values[2] - 419.5714286).abs() < 1e-5);
        assert!((ts2.values[3] - 592.4285714).abs() < 1e-5);
        assert!((ts2.values[4] - 746.5714286).abs() < 1e-5);
        assert!((ts2.values[5] - 923.0).abs() < 1e-5);
        assert!((ts2.values[6] - 1105.0).abs() < 1e-5);
        assert!((ts2.values[7] - 1352.0).abs() < 1e-5);

        // Test weeks to months
        ts2 = ts1.change_periodicity(&tlm, AggType::Add).unwrap();
        assert!((ts2.values[0] - 7.714285714).abs() < 1e-5);
        assert!((ts2.values[1] - 23.71428571).abs() < 1e-5);
        assert!((ts2.values[2] - 44.85714286).abs() < 1e-5);
        assert!((ts2.values[3] - 62.14285714).abs() < 1e-5);
        assert!((ts2.values[4] - 83.57142857).abs() < 1e-5);
        assert!((ts2.values[5] - 99.42857143).abs() < 1e-5);
        assert!((ts2.values[6] - 122.1428571).abs() < 1e-5);
        assert!((ts2.values[7] - 141.7142857).abs() < 1e-5);
        assert!((ts2.values[8] - 155.7142857).abs() < 1e-5);
        assert!((ts2.values[9] - 180.4285714).abs() < 1e-5);
        assert!((ts2.values[10] - 193.1428571).abs() < 1e-5);
        assert!((ts2.values[11] - 218.8571429).abs() < 1e-5);
        assert!((ts2.values[12] - 238.5714286).abs() < 1e-5);
        assert!((ts2.values[13] - 232.2857143).abs() < 1e-5);
        assert!((ts2.values[14] - 275.7142857).abs() < 1e-5);
        assert!((ts2.values[15] - 285.7142857).abs() < 1e-5);
        assert!((ts2.values[16] - 314.4285714).abs() < 1e-5);
        assert!((ts2.values[17] - 322.8571429).abs() < 1e-5);
        assert!((ts2.values[18] - 353.1428571).abs() < 1e-5);
        assert!((ts2.values[19] - 372.5714286).abs() < 1e-5);
        assert!((ts2.values[20] - 379.2857143).abs() < 1e-5);
        assert!((ts2.values[21] - 411.2857143).abs() < 1e-5);
        assert!((ts2.values[22] - 416.5714286).abs() < 1e-5);
        assert!((ts2.values[23] - 524.1428571).abs() < 1e-5);

        // Create a daily timeseries
        let tl4 = Timeline::new(dr, Period::Day);
        v = Vec::new();
        for i in 0..730 {
            v.push(i);
        }
        ts1 = TimeSeries::new(&tl4, v).unwrap().cast_f64();

        // Test days to years
        ts2 = ts1.change_periodicity(&tly, AggType::Add).unwrap();
        assert_eq!(ts2.values, vec![66430.0, 199655.0]);

        // Test days to quarters
        ts2 = ts1.change_periodicity(&tlq, AggType::Add).unwrap();
        assert_eq!(
            ts2.values,
            vec![4005.0, 12285.0, 20838.0, 29302.0, 36855.0, 45500.0, 54418.0, 62882.0]
        );

        // Test days to months
        ts2 = ts1.change_periodicity(&tlm, AggType::Add).unwrap();
        assert_eq!(
            ts2.values,
            vec![
                465.0, 1246.0, 2294.0, 3135.0, 4185.0, 4965.0, 6076.0, 7037.0, 7725.0, 8928.0,
                9555.0, 10819.0, 11780.0, 11466.0, 13609.0, 14085.0, 15500.0, 15915.0, 17391.0,
                18352.0, 18675.0, 20243.0, 20505.0, 22134.0
            ]
        );

        // Test days to weeks
        ts2 = ts1.change_periodicity(&tlw, AggType::Add).unwrap();
        assert_eq!(
            ts2.values,
            vec![
                21.0, 70.0, 119.0, 168.0, 217.0, 266.0, 315.0, 364.0, 413.0, 462.0, 511.0, 560.0,
                609.0, 658.0, 707.0, 756.0, 805.0, 854.0, 903.0, 952.0, 1001.0, 1050.0, 1099.0,
                1148.0, 1197.0, 1246.0, 1295.0, 1344.0, 1393.0, 1442.0, 1491.0, 1540.0, 1589.0,
                1638.0, 1687.0, 1736.0, 1785.0, 1834.0, 1883.0, 1932.0, 1981.0, 2030.0, 2079.0,
                2128.0, 2177.0, 2226.0, 2275.0, 2324.0, 2373.0, 2422.0, 2471.0, 2520.0, 2569.0,
                2618.0, 2667.0, 2716.0, 2765.0, 2814.0, 2863.0, 2912.0, 2961.0, 3010.0, 3059.0,
                3108.0, 3157.0, 3206.0, 3255.0, 3304.0, 3353.0, 3402.0, 3451.0, 3500.0, 3549.0,
                3598.0, 3647.0, 3696.0, 3745.0, 3794.0, 3843.0, 3892.0, 3941.0, 3990.0, 4039.0,
                4088.0, 4137.0, 4186.0, 4235.0, 4284.0, 4333.0, 4382.0, 4431.0, 4480.0, 4529.0,
                4578.0, 4627.0, 4676.0, 4725.0, 4774.0, 4823.0, 4872.0, 4921.0, 4970.0, 5019.0,
                5068.0, 1457.0
            ]
        );
    }

    #[test]
    fn change_periodicity_add_down_f64() {
        // Create a date range
        let from = Date::from_calendar_date(2022, Month::January, 1).unwrap();
        let dur = Duration::new(0, 0, 2);
        let dr = DateRange::from_duration(from, dur).unwrap();

        // Create timelines to resize to
        let tlq = Timeline::new(dr, Period::Quarter);
        let tlm = Timeline::new(dr, Period::Month);
        let tlw = Timeline::new(dr, Period::Week);
        let tld = Timeline::new(dr, Period::Day);

        // Create a yearly timeseries
        let tl1 = Timeline::new(dr, Period::Year);
        let v = vec![1, 2];
        let ts1 = TimeSeries::new(&tl1, v).unwrap().cast_f64();

        // Test years to quarters
        let mut ts2 = ts1.change_periodicity(&tlq, AggType::Add).unwrap();
        assert!((ts2.values[0] - 0.25).abs() < 1e-10);
        assert!((ts2.values[3] - 0.25).abs() < 1e-10);
        assert!((ts2.values[4] - 0.5).abs() < 1e-10);
        assert!((ts2.values[7] - 0.5).abs() < 1e-10);

        // Test years to months
        ts2 = ts1.change_periodicity(&tlm, AggType::Add).unwrap();
        assert!((ts2.values[0] - 0.083333333333).abs() < 1e-10);
        assert!((ts2.values[11] - 0.083333333333).abs() < 1e-10);
        assert!((ts2.values[12] - 0.166666666666).abs() < 1e-10);
        assert!((ts2.values[23] - 0.166666666666).abs() < 1e-10);

        // Test years to weeks
        ts2 = ts1.change_periodicity(&tlw, AggType::Add).unwrap();
        assert!((ts2.values[0] - 0.019178082192).abs() < 1e-10);
        assert!((ts2.values[51] - 0.019178082192).abs() < 1e-10);
        assert!((ts2.values[52] - 0.035172158460).abs() < 1e-10);
        assert!((ts2.values[53] - 0.037837837838).abs() < 1e-10);
        assert!((ts2.values[104] - 0.037837837838).abs() < 1e-10);

        // Test years to days
        ts2 = ts1.change_periodicity(&tld, AggType::Add).unwrap();
        assert!((ts2.values[0] - 0.002739726027).abs() < 1e-10);
        assert!((ts2.values[364] - 0.002739726027).abs() < 1e-10);
        assert!((ts2.values[365] - 0.005479452055).abs() < 1e-10);
        assert!((ts2.values[729] - 0.005479452055).abs() < 1e-10);

        // TODO: test from other periodicity than years ... maybe
    }

    #[test]
    fn update() {
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = Timeline::new(dr, Period::Quarter);

        // Create a timeseries
        let v1 = vec![1, 2, 3, 4];
        let mut ts1 = TimeSeries::new(&tl, v1).unwrap();

        // Before
        let mut d = Date::from_calendar_date(2022, Month::January, 9).unwrap();
        ts1.update((d, 1000));
        assert_eq!(ts1.values, vec![1, 2, 3, 4]);

        // First day
        d = from;
        ts1.update((d, 100));
        assert_eq!(ts1.values, vec![100, 2, 3, 4]);

        // Middle
        d = Date::from_calendar_date(2022, Month::April, 10).unwrap();
        ts1.update((d, -5));
        assert_eq!(ts1.values, vec![100, -5, 3, 4]);

        // Last day
        d = dr.last_day();
        ts1.update((d, 0));
        assert_eq!(ts1.values, vec![100, -5, 3, 0]);

        // After
        d = to;
        ts1.update((d, 200));
        assert_eq!(ts1.values, vec![100, -5, 3, 0]);
    }

    #[test]
    fn update_add() {
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = Timeline::new(dr, Period::Quarter);

        // Create a timeseries
        let v1 = vec![1, 2, 3, 4];
        let mut ts1 = TimeSeries::new(&tl, v1).unwrap();

        // Before
        let mut d = Date::from_calendar_date(2022, Month::January, 9).unwrap();
        ts1.update_add((d, 1000));
        assert_eq!(ts1.values, vec![1, 2, 3, 4]);

        // First day
        d = from;
        ts1.update_add((d, 100));
        assert_eq!(ts1.values, vec![101, 2, 3, 4]);

        // Middle
        d = Date::from_calendar_date(2022, Month::April, 10).unwrap();
        ts1.update_add((d, -5));
        assert_eq!(ts1.values, vec![101, -3, 3, 4]);

        // Last day
        d = dr.last_day();
        ts1.update_add((d, -4));
        assert_eq!(ts1.values, vec![101, -3, 3, 0]);

        // After
        d = to;
        ts1.update_add((d, 200));
        assert_eq!(ts1.values, vec![101, -3, 3, 0]);
    }

    #[test]
    fn shift_years() {
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2030, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = Timeline::new(dr, Period::Year);

        // Create a timeseries
        let v1 = vec![1, 2, 3, 4, 5, 6, 7, 8];
        let ts1 = TimeSeries::new(&tl, v1).unwrap();

        // Create a shift duration and apply it
        let mut shift = Duration::new(0, 0, 4);
        let mut tsr = ts1.shift(shift, 0);
        assert!(tsr.is_ok());
        let mut ts2 = tsr.unwrap();
        assert_eq!(ts2.values, vec![5, 6, 7, 8, 0, 0, 0, 0]);

        // Test negative shift duration
        shift = Duration::new(0, 0, -4);
        ts2 = ts1.shift(shift, 0).unwrap();
        assert_eq!(ts2.values, vec![0, 0, 0, 0, 1, 2, 3, 4]);

        // Test different pad value
        shift = Duration::new(0, 0, -4);
        ts2 = ts1.shift(shift, 1000).unwrap();
        assert_eq!(ts2.values, vec![1000, 1000, 1000, 1000, 1, 2, 3, 4]);

        // Test with shift greater than timeline
        shift = Duration::new(0, 0, 100);
        ts2 = ts1.shift(shift, 0).unwrap();
        assert_eq!(ts2.values, vec![0; tl.len as usize]);
        shift = Duration::new(0, 0, -100);
        ts2 = ts1.shift(shift, 0).unwrap();
        assert_eq!(ts2.values, vec![0; tl.len as usize]);

        // Test duration with days: should error
        shift = Duration::new(1, 0, 1);
        tsr = ts1.shift(shift, 0);
        assert!(tsr.is_err());

        // Test duration with months: should error
        shift = Duration::new(0, 5, 4);
        tsr = ts1.shift(shift, 0);
        assert!(tsr.is_err());

        // Test with zero duration
        shift = Duration::new(0, 0, 0);
        ts2 = ts1.shift(shift, 0).unwrap();
        assert_eq!(ts2, ts1);
    }

    #[test]
    fn shift_quarters() {
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2024, Month::January, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = Timeline::new(dr, Period::Quarter);

        // Create a timeseries
        let v1 = vec![1, 2, 3, 4, 5, 6, 7, 8];
        let ts1 = TimeSeries::new(&tl, v1).unwrap();

        // Create a shift duration and apply it
        let mut shift = Duration::new(0, 9, 0);
        let mut tsr = ts1.shift(shift, 0);
        assert!(tsr.is_ok());
        let mut ts2 = tsr.unwrap();
        assert_eq!(ts2.values, vec![4, 5, 6, 7, 8, 0, 0, 0]);

        // Test negative shift duration
        shift = Duration::new(0, -9, 0);
        ts2 = ts1.shift(shift, 0).unwrap();
        assert_eq!(ts2.values, vec![0, 0, 0, 1, 2, 3, 4, 5]);

        // Test different pad value
        shift = Duration::new(0, -9, 0);
        ts2 = ts1.shift(shift, 1000).unwrap();
        assert_eq!(ts2.values, vec![1000, 1000, 1000, 1, 2, 3, 4, 5]);

        // Test with shift greater than timeline
        shift = Duration::new(0, 99, 0);
        ts2 = ts1.shift(shift, 0).unwrap();
        assert_eq!(ts2.values, vec![0; tl.len as usize]);
        shift = Duration::new(0, -99, 0);
        ts2 = ts1.shift(shift, 0).unwrap();
        assert_eq!(ts2.values, vec![0; tl.len as usize]);

        // Test years and months mixed
        shift = Duration::new(0, -9, -1);
        ts2 = ts1.shift(shift, 0).unwrap();
        assert_eq!(ts2.values, vec![0, 0, 0, 0, 0, 0, 0, 1]);

        // Test duration with days: should error
        shift = Duration::new(1, 9, 0);
        tsr = ts1.shift(shift, 0);
        assert!(tsr.is_err());

        // Test duration with bad months: should error
        shift = Duration::new(0, 5, 0);
        tsr = ts1.shift(shift, 0);
        assert!(tsr.is_err());

        // Test with zero duration
        shift = Duration::new(0, 0, 0);
        ts2 = ts1.shift(shift, 0).unwrap();
        assert_eq!(ts2, ts1);
    }

    #[test]
    fn shift_months() {
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2023, Month::August, 10).unwrap();
        let dr = DateRange::new(from, to);
        let tl = Timeline::new(dr, Period::Month);

        // Create a timeseries
        let v1 = vec![
            1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
        ];
        let ts1 = TimeSeries::new(&tl, v1).unwrap();

        // Create a shift duration and apply it
        let mut shift = Duration::new(0, 3, 0);
        let mut tsr = ts1.shift(shift, 0);
        assert!(tsr.is_ok());
        let mut ts2 = tsr.unwrap();
        assert_eq!(
            ts2.values,
            vec![4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 0, 0, 0]
        );

        // Test negative shift duration
        shift = Duration::new(0, -3, 0);
        ts2 = ts1.shift(shift, 0).unwrap();
        assert_eq!(
            ts2.values,
            vec![0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
        );

        // Test different pad value
        shift = Duration::new(0, -3, 0);
        ts2 = ts1.shift(shift, 1000).unwrap();
        assert_eq!(
            ts2.values,
            vec![1000, 1000, 1000, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
        );

        // Test with shift greater than timeline
        shift = Duration::new(0, 100, 0);
        ts2 = ts1.shift(shift, 0).unwrap();
        assert_eq!(ts2.values, vec![0; tl.len as usize]);
        shift = Duration::new(0, -100, 0);
        ts2 = ts1.shift(shift, 0).unwrap();
        assert_eq!(ts2.values, vec![0; tl.len as usize]);

        // Test years and months mixed
        shift = Duration::new(0, -5, -1);
        ts2 = ts1.shift(shift, 0).unwrap();
        assert_eq!(
            ts2.values,
            vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2]
        );

        // Test duration with days: should error
        shift = Duration::new(1, 9, 0);
        tsr = ts1.shift(shift, 0);
        assert!(tsr.is_err());

        // Test with zero duration
        shift = Duration::new(0, 0, 0);
        ts2 = ts1.shift(shift, 0).unwrap();
        assert_eq!(ts2, ts1);
    }

    #[test]
    fn shift_weeks() {
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 10).unwrap();
        let to = Date::from_calendar_date(2022, Month::March, 7).unwrap();
        let dr = DateRange::new(from, to);
        let tl = Timeline::new(dr, Period::Week);

        // Create a timeseries
        let v1 = vec![1, 2, 3, 4, 5, 6, 7, 8];
        let ts1 = TimeSeries::new(&tl, v1).unwrap();

        // Create a shift duration and apply it
        let mut shift = Duration::new(21, 0, 0);
        let mut tsr = ts1.shift(shift, 0);
        assert!(tsr.is_ok());
        let mut ts2 = tsr.unwrap();
        assert_eq!(ts2.values, vec![4, 5, 6, 7, 8, 0, 0, 0]);

        // Test negative shift duration
        shift = Duration::new(-21, 0, 0);
        ts2 = ts1.shift(shift, 0).unwrap();
        assert_eq!(ts2.values, vec![0, 0, 0, 1, 2, 3, 4, 5]);

        // Test different pad value
        shift = Duration::new(-21, 0, 0);
        ts2 = ts1.shift(shift, 1000).unwrap();
        assert_eq!(ts2.values, vec![1000, 1000, 1000, 1, 2, 3, 4, 5]);

        // Test with shift greater than timeline
        shift = Duration::new(98, 0, 0);
        ts2 = ts1.shift(shift, 0).unwrap();
        assert_eq!(ts2.values, vec![0; tl.len as usize]);
        shift = Duration::new(-98, 0, 0);
        ts2 = ts1.shift(shift, 0).unwrap();
        assert_eq!(ts2.values, vec![0; tl.len as usize]);

        // Test duration with months: should error
        shift = Duration::new(14, 9, 0);
        tsr = ts1.shift(shift, 0);
        assert!(tsr.is_err());

        // Test duration with years: should error
        shift = Duration::new(14, 0, 8);
        tsr = ts1.shift(shift, 0);
        assert!(tsr.is_err());

        // Test duration with bad days: should error
        shift = Duration::new(20, 0, 0);
        tsr = ts1.shift(shift, 0);
        assert!(tsr.is_err());

        // Test with zero duration
        shift = Duration::new(0, 0, 0);
        ts2 = ts1.shift(shift, 0).unwrap();
        assert_eq!(ts2, ts1);
    }

    #[test]
    fn shift_days() {
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::February, 25).unwrap();
        let to = Date::from_calendar_date(2022, Month::March, 5).unwrap();
        let dr = DateRange::new(from, to);
        let tl = Timeline::new(dr, Period::Day);

        // Create a timeseries
        let v1 = vec![1, 2, 3, 4, 5, 6, 7, 8];
        let ts1 = TimeSeries::new(&tl, v1).unwrap();

        // Create a shift duration and apply it
        let mut shift = Duration::new(4, 0, 0);
        let mut tsr = ts1.shift(shift, 0);
        assert!(tsr.is_ok());
        let mut ts2 = tsr.unwrap();
        assert_eq!(ts2.values, vec![5, 6, 7, 8, 0, 0, 0, 0]);

        // Test negative shift duration
        shift = Duration::new(-4, 0, 0);
        ts2 = ts1.shift(shift, 0).unwrap();
        assert_eq!(ts2.values, vec![0, 0, 0, 0, 1, 2, 3, 4]);

        // Test different pad value
        shift = Duration::new(-4, 0, 0);
        ts2 = ts1.shift(shift, 1000).unwrap();
        assert_eq!(ts2.values, vec![1000, 1000, 1000, 1000, 1, 2, 3, 4]);

        // Test with shift greater than timeline
        shift = Duration::new(100, 0, 0);
        ts2 = ts1.shift(shift, 0).unwrap();
        assert_eq!(ts2.values, vec![0; tl.len as usize]);
        shift = Duration::new(-100, 0, 0);
        ts2 = ts1.shift(shift, 0).unwrap();
        assert_eq!(ts2.values, vec![0; tl.len as usize]);

        // Test duration with years: should error
        shift = Duration::new(10, 0, 1);
        tsr = ts1.shift(shift, 0);
        assert!(tsr.is_err());

        // Test duration with months: should error
        shift = Duration::new(21, 9, 0);
        tsr = ts1.shift(shift, 0);
        assert!(tsr.is_err());

        // Test with zero duration
        shift = Duration::new(0, 0, 0);
        ts2 = ts1.shift(shift, 0).unwrap();
        assert_eq!(ts2, ts1);
    }

    #[test]
    fn apply() {
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
    fn apply_with_time() {
        // Create a timeline
        let from = Date::from_calendar_date(2022, Month::January, 1).unwrap();
        let dur = Duration::new(0, 0, 2);
        let dr = DateRange::from_duration(from, dur).unwrap();
        let tl = Timeline::new(dr, Period::Quarter);

        // Create two timeseries
        let v1 = vec![1, 2, 3, 4, 1, 2, 3, 4];
        let ts1 = TimeSeries::new(&tl, v1).unwrap();
        let v2 = vec![5, 6, 7, 8, 9, 10, 11, 12];
        let ts2 = TimeSeries::new(&tl, v2).unwrap();

        // Create a date
        let date = (from + Duration::new(0, 4, 1)).unwrap().primary();
        // Write a generic function that can be pairwise applied to the elements of a TS and check OK
        let op = |(t, &a, &b): (DateRange, &i32, &i32)| -> i32 {
            if t.contains(date) {
                1000
            } else if a < 3 {
                1
            } else {
                b + 1
            }
        };
        let ts3 = ts1.apply_with_time(&ts2, op);
        assert!(ts3.is_ok());

        // Check values in added TS
        let ts3 = ts3.unwrap();
        assert_eq!(ts3.values, vec![1, 1, 8, 9, 1, 1000, 12, 13]);

        // Check adding TS with different timeline is not OK
        let tl2 = Timeline::new(dr, Period::Year);
        let v4 = vec![1, 2];
        let ts4 = TimeSeries::new(&tl2, v4).unwrap();
        let ts5 = ts4.apply_with_time(&ts1, op);
        assert!(ts5.is_err());
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

    #[test]
    fn iterator() {
        // Create a quarterly timeseries
        let from = Date::from_calendar_date(2022, Month::January, 1).unwrap();
        let dur = Duration::new(0, 0, 2);
        let dr = DateRange::from_duration(from, dur).unwrap();
        let tl1 = Timeline::new(dr, Period::Quarter);
        let v = vec![1, 2, 3, 4, 5, 6, 7, 8];
        let ts1 = TimeSeries::new(&tl1, v).unwrap();

        // Test a for loop
        let q = Duration::new(0, 3, 0);
        for (i, (drp, val)) in ts1.into_iter().enumerate() {
            match i {
                0 => {
                    let d = Date::from_calendar_date(2022, Month::January, 1).unwrap();
                    assert_eq!(drp, DateRange::from_duration(d, q).unwrap());
                    assert_eq!(val, &1);
                }
                1 => {
                    let d = Date::from_calendar_date(2022, Month::April, 1).unwrap();
                    assert_eq!(drp, DateRange::from_duration(d, q).unwrap());
                    assert_eq!(val, &2);
                }
                2 => {
                    let d = Date::from_calendar_date(2022, Month::July, 1).unwrap();
                    assert_eq!(drp, DateRange::from_duration(d, q).unwrap());
                    assert_eq!(val, &3);
                }
                3 => {
                    let d = Date::from_calendar_date(2022, Month::October, 1).unwrap();
                    assert_eq!(drp, DateRange::from_duration(d, q).unwrap());
                    assert_eq!(val, &4);
                }
                4 => {
                    let d = Date::from_calendar_date(2023, Month::January, 1).unwrap();
                    assert_eq!(drp, DateRange::from_duration(d, q).unwrap());
                    assert_eq!(val, &5);
                }
                5 => {
                    let d = Date::from_calendar_date(2023, Month::April, 1).unwrap();
                    assert_eq!(drp, DateRange::from_duration(d, q).unwrap());
                    assert_eq!(val, &6);
                }
                6 => {
                    let d = Date::from_calendar_date(2023, Month::July, 1).unwrap();
                    assert_eq!(drp, DateRange::from_duration(d, q).unwrap());
                    assert_eq!(val, &7);
                }
                7 => {
                    let d = Date::from_calendar_date(2023, Month::October, 1).unwrap();
                    assert_eq!(drp, DateRange::from_duration(d, q).unwrap());
                    assert_eq!(val, &8);
                }
                _ => {
                    unreachable!();
                }
            }
        }
        assert_eq!(ts1.into_iter().map(|(_, v)| v).sum::<i32>(), 36);
    }
}
