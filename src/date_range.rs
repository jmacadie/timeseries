use time::Date;
use std::cmp;

/// # DateRange
/// 
/// Simply comprises a pair of [`time::Date`] objects that represent
/// the start and end of a date range
/// 
/// ---
/// ### To be implemented...
/// This object allows us to implement a `date_diff` function that is
/// aware of intervals of a month and upwards, which is missing from
/// [`time`]
/// 
/// Also by using the alternate constructor that takes a start date
/// and \[chunks of period, defined somehow\] we will effectively be
/// able to implement a `date_add` function
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DateRange {
    pub(crate) from: Date,
    pub(crate) to: Date,
}

impl DateRange {
    
    // TODO: write another constructor that takes a start date and a duration, rather just from and two
    //  this will allow the DateRange object to more naturally fit with the Timeline object and avoid
    //  the problem of stub periods when the two do not fit together
    //  This would also allow us to get round the missing date_add method from Date for Durations above a week

    // TODO: write methods to export how many days/weeks/months/years a DateRange covers
    // This would effectively enable a date_diff method extension on Date

    pub fn new(from: Date, to: Date) -> Self {
        if from < to {
            Self {from, to}
        } else {
            Self {to, from}
        }
    }

    pub fn from(&self) -> &Date {
        &self.from
    }

    pub fn to(&self) -> &Date {
        &self.to
    }

    pub fn intersect(&self, other: &DateRange) -> Option<DateRange> {
        if other.from > self.to || other.to < self.from {
            None
        } else {
            let from = cmp::max(self.from, other.from);
            let to = cmp::max(self.to, other.to);
            Some(DateRange::new(from, to))
        }
    }
    
    pub fn union(&self, other: &DateRange) -> DateRange {
        let from = cmp::min(self.from, other.from);
        let to = cmp::max(self.to, other.to);
        DateRange::new(from, to)
    }

    pub fn contains(&self, date: &Date) -> bool {
        if self.from <= *date && self.to >= *date {
            return true;
        }
        false
    }

}
