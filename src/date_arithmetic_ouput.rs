use core::fmt;
use time::Date;

/// # `DateArithmeticOutput`
///
/// The requirement for `Date` plus / minus a `Duration`
/// to be reversible _e.g. 30th Mar minus 1 month is
/// 28th Feb, so 28th Feb has to (at least) equal 30th
/// Mar_ gives rise to multiple possible results for
/// some additions and subtractions. To handle this
/// ambiguity, we use this struct to wrap a vector of
/// all possible results from the arithmetic operation.
///
/// See `Duration` documentation for further explanation
///
/// The most likely result can always be accessed by
/// calling the `.primary()` method
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DateArithmeticOutput {
    values: Vec<Date>,
}

impl DateArithmeticOutput {
    #[must_use]
    pub fn new(date: Date) -> Self {
        let values = vec![date];
        Self { values }
    }

    pub fn append(&mut self, date: Date) {
        self.values.push(date);
    }

    #[must_use]
    pub fn contains(&self, date: Date) -> bool {
        self.values.contains(&date)
    }

    #[must_use]
    pub fn primary(&self) -> Date {
        self.values[0]
    }

    #[must_use]
    pub fn value(&self, idx: u8) -> Option<Date> {
        let d = *self.values.get(idx as usize)?;
        Some(d)
    }
}

// region: formatting
impl fmt::Display for DateArithmeticOutput {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut output = String::new();
        for d in &self.values {
            output.push_str(&format!("{}; ", d));
        }
        if output.chars().count() > 0 {
            output.pop();
            output.pop();
        }
        f.write_str(&output)
    }
}
// endregion formatting

// region: iterator

// region: owned_iterator
pub struct IntoIter {
    values: Vec<Date>,
}

impl Iterator for IntoIter {
    type Item = Date;

    fn next(&mut self) -> Option<Self::Item> {
        if self.values.is_empty() {
            return None;
        }
        Some(self.values.remove(0))
    }
}

impl IntoIterator for DateArithmeticOutput {
    type Item = Date;
    type IntoIter = IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            values: self.values,
        }
    }
}
// endregion owend_iterator

// region: ref_iterator
pub struct Iter<'a> {
    values: &'a [Date],
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a Date;

    fn next(&mut self) -> Option<Self::Item> {
        let (val, tail) = self.values.split_first()?;
        self.values = tail;
        Some(val)
    }
}

impl<'a> DateArithmeticOutput {
    #[must_use]
    pub fn iter(&'a self) -> Iter<'a> {
        Iter {
            values: &self.values[..],
        }
    }
}

impl<'a> IntoIterator for &'a DateArithmeticOutput {
    type Item = &'a Date;
    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
// endregion ref_iterator

// region: mutref_iterator
pub struct IterMut<'a> {
    values: &'a mut [Date],
}

impl<'a> Iterator for IterMut<'a> {
    type Item = &'a mut Date;

    fn next(&mut self) -> Option<Self::Item> {
        let values = std::mem::take(&mut self.values);
        let (val, tail) = values.split_first_mut()?;
        self.values = tail;
        Some(val)
    }
}

impl<'a> DateArithmeticOutput {
    #[must_use]
    pub fn iter_mut(&'a mut self) -> IterMut<'a> {
        IterMut {
            values: &mut self.values[..],
        }
    }
}

impl<'a> IntoIterator for &'a mut DateArithmeticOutput {
    type Item = &'a mut Date;
    type IntoIter = IterMut<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}
// endregion mutref_iterator

// endregion iterator

#[cfg(test)]
mod tests {
    use super::*;
    use time::Month;

    #[test]
    fn new() {
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let dao = DateArithmeticOutput::new(d1);
        assert_eq!(dao.values[0], d1);
        assert_eq!(dao.values.len(), 1);
    }

    #[test]
    fn append() {
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let d2 = Date::from_calendar_date(2023, Month::January, 15).unwrap();
        let d3 = Date::from_calendar_date(2024, Month::January, 15).unwrap();
        let mut dao = DateArithmeticOutput::new(d1);

        // Append a date & check
        dao.append(d2);
        assert_eq!(dao.values[0], d1);
        assert_eq!(dao.values[1], d2);
        assert_eq!(dao.values.len(), 2);

        // Append another date & check again
        dao.append(d3);
        assert_eq!(dao.values[0], d1);
        assert_eq!(dao.values[1], d2);
        assert_eq!(dao.values[2], d3);
        assert_eq!(dao.values.len(), 3);
    }

    #[test]
    fn contains() {
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let d2 = Date::from_calendar_date(2023, Month::January, 15).unwrap();
        let d3 = Date::from_calendar_date(2024, Month::January, 15).unwrap();
        let d4 = Date::from_calendar_date(2025, Month::January, 15).unwrap();

        let mut dao = DateArithmeticOutput::new(d1);
        dao.append(d2);
        dao.append(d3);

        assert!(dao.contains(d1));
        assert!(dao.contains(d2));
        assert!(dao.contains(d3));
        assert!(!dao.contains(d4));
    }

    #[test]
    fn primary() {
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let d2 = Date::from_calendar_date(2023, Month::January, 15).unwrap();
        let d3 = Date::from_calendar_date(2024, Month::January, 15).unwrap();
        let d4 = Date::from_calendar_date(2025, Month::January, 15).unwrap();

        let mut dao = DateArithmeticOutput::new(d1);
        dao.append(d2);
        dao.append(d3);

        assert_eq!(dao.primary(), d1);
        assert_ne!(dao.primary(), d2);
        assert_ne!(dao.primary(), d3);
        assert_ne!(dao.primary(), d4);
    }

    #[test]
    fn value() {
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let d2 = Date::from_calendar_date(2023, Month::January, 15).unwrap();
        let d3 = Date::from_calendar_date(2024, Month::January, 15).unwrap();

        let mut dao = DateArithmeticOutput::new(d1);
        dao.append(d2);
        dao.append(d3);

        // Test regular access
        assert_eq!(dao.value(0), Some(d1));
        assert_eq!(dao.value(1), Some(d2));
        assert_eq!(dao.value(2), Some(d3));
        assert_eq!(dao.value(3), None);
    }

    #[test]
    fn format() {
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let d2 = Date::from_calendar_date(2023, Month::January, 15).unwrap();
        let d3 = Date::from_calendar_date(2024, Month::January, 15).unwrap();

        let mut dao = DateArithmeticOutput::new(d1);
        dao.append(d2);
        dao.append(d3);

        assert_eq!(format!("{}", dao), "2022-01-15; 2023-01-15; 2024-01-15");
    }

    #[test]
    fn iterator() {
        let d1 = Date::from_calendar_date(2022, Month::January, 15).unwrap();
        let d2 = Date::from_calendar_date(2023, Month::January, 15).unwrap();
        let d3 = Date::from_calendar_date(2024, Month::January, 15).unwrap();

        let mut dao = DateArithmeticOutput::new(d1);
        dao.append(d2);
        dao.append(d3);

        // Test reference version in for loop
        for (i, d) in dao.iter().enumerate() {
            match i {
                0 => {
                    assert_eq!(*d, d1);
                }
                1 => {
                    assert_eq!(*d, d2);
                }
                2 => {
                    assert_eq!(*d, d3);
                }
                _ => {
                    unreachable!();
                }
            }
        }

        // Test owned version in for loop
        for (i, d) in dao.into_iter().enumerate() {
            match i {
                0 => {
                    assert_eq!(d, d1);
                }
                1 => {
                    assert_eq!(d, d2);
                }
                2 => {
                    assert_eq!(d, d3);
                }
                _ => {
                    unreachable!();
                }
            }
        }
    }
}
