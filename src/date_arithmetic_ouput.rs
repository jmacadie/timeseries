use time::Date;
use std::convert::TryFrom;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DateArithmeticOutput {
    values: Vec<Date>,
    index: u8,
}

impl DateArithmeticOutput {

    pub fn new(date: Date) -> Self {
        let values = vec![date];
        Self { values, index: 0_u8 }
    }

    pub fn add(&mut self, date: Date) -> () {
        self.values.push(date);
    }

    pub fn contains(&self, date: Date) -> bool {
        for d in self.values.iter() {
            if *d == date { return true; }
        }
        return false;
    }

    pub fn primary(&self) -> Date {
        return self.values[0].clone();
    }

    pub fn value(&self, idx: u8) -> Option<Date> {
        match self.len() {
            Some(l) => {
                if (idx + 1) > l {
                    return None;
                } else {
                    return Some(self.values[idx as usize].clone());
                }
            },
            None => { return None; },
        };
    }

    fn len(&self) -> Option<u8> {
        match u8::try_from(self.values.len()) {
            Ok(l) => { return Some(l); },
            Err(_) => { return None; },
        };
    }

}

impl Iterator for DateArithmeticOutput {
    type Item = Date;

    fn next(&mut self) -> Option<Self::Item> {
        let i = match u8::try_from(self.values.len()) {
            Ok(l) => l - 1,
            Err(_) => { return None; },
        };
        match self.index {
            i => None,
            _ => {
                self.index += 1;
                Some(self.values[(self.index - 1) as usize].clone())
            }
        }
    }

}

