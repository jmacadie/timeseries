use time::Date;
use std::convert::TryFrom;
use core::fmt;

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

    pub fn append(&mut self, date: Date) -> () {
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

impl fmt::Display for DateArithmeticOutput {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut output = String::new();
        for d in self.values.clone().iter() {
            output.push_str(&format!("{}; ", d));
        }
        f.write_str(&output)
    }
}

impl Iterator for DateArithmeticOutput {
    type Item = Date;

    // TODO: Fix. This isn't working
    fn next(&mut self) -> Option<Self::Item> {
        let max = match self.len() {
            Some(l) => l - 1,
            None => { return None; },
        };
        if self.index >= max {
            None
        } else {
            self.index += 1;
            Some(self.values[(self.index - 1) as usize].clone())
        }
    }

}

