/*
pub struct DurationExt {
    base: time::Duration, // can hold vaules of up to 4 weeks in, so we will use this stuct to handle all durations
    months: i8,
    years: i32,
}

const MAX_DURATION: time::Duration = time::Duration::weeks(4);

impl DurationExt {


    pub fn new(duration: time::Duration, months: i8, years: i32) -> Result<Self, &'static str> {
        if duration > MAX_DURATION {
            return Err("Duration longer than 4 weeks. Can't reliably convert to months and years");
        }
        Ok(DurationExt {
            base: time::Duration::new(0, 0),
            months,
            years,
        })
    }
    
}*/
