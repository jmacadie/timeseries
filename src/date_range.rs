use time::Date;
use std::cmp;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DateRange {
    pub(crate) from: Date,
    pub(crate) to: Date,
}

impl DateRange {
    
    // TODO: write another constructor that takes a start date and a duration, rather just from and two
    //  this will allow the DateRange object to more naturally fit with the Timeline object and avoid
    //  the problem of stub periods when the two do not fit together

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
