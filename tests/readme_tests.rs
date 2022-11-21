use timeseries::*;

#[test]
#[allow(unused_assignments)]
fn readme_duration() {
    use time::{Date, Month};

    // Durations can be created directly ...
    let mut dur = Duration::new(1, 2, 3); // 3 years, 2 months and 1 day

    // ... from a pair of dates ...
    let d1 = Date::from_calendar_date(2022, Month::January, 1).unwrap();
    let d2 = Date::from_calendar_date(2025, Month::March, 2).unwrap();
    dur = Duration::from_dates(d1, d2); // 3 years, 2 months and 1 day

    // ... or from a time::Duration
    let td = time::Duration::weeks(2);
    dur = Duration::from_time_duration(td).unwrap(); // 14 days

    // The days, months and years part can be extracted
    assert_eq!(dur.days(), 14);
    assert_eq!(dur.months(), 0);
    assert_eq!(dur.years(), 0);

    // The parts can overflow ...
    dur = Duration::new(400, 0, 0);
    assert_eq!(dur.days(), 400);
    assert_eq!(dur.months(), 0);
    assert_eq!(dur.years(), 0);

    // ... use normalise() to, well, normalise them
    // has to be done from a reference date though
    let norm = dur.normalise(d1).unwrap();
    assert_eq!(norm.days(), 4);
    assert_eq!(norm.months(), 1);
    assert_eq!(norm.years(), 1);

    // Durations go both forwards in time & backwards, use invert to flip the sign
    let back = norm.invert();
    assert_eq!(back.days(), -4);
    assert_eq!(back.months(), -1);
    assert_eq!(back.years(), -1);

    // Use forwards to test the direction
    assert!(norm.forwards());
    assert!(!back.forwards());

    // Durations can be added to Dates
    // The operation can fail (in edge cases with massive dates), which sadly hurts the ergonomics
    // Also can potentially return multiple results, use primary() to access the most likely
    let mut d3 = (d1 + norm).unwrap().primary();
    assert_eq!((d3.year(), d3.month() as u8, d3.day()), (2023, 2, 5));
    d3 = (d1 + dur).unwrap().primary();
    assert_eq!((d3.year(), d3.month() as u8, d3.day()), (2023, 2, 5));

    // Addition (and subtraction) can result in multiple values
    let d3 = Date::from_calendar_date(2022, Month::February, 28).unwrap();
    dur = Duration::new(0, 1, 0); // 1 month
    let dao = (d3 + dur).unwrap();
    assert!(dao.contains(Date::from_calendar_date(2022, Month::March, 28).unwrap()));
    assert!(dao.contains(Date::from_calendar_date(2022, Month::March, 29).unwrap()));
    assert!(dao.contains(Date::from_calendar_date(2022, Month::March, 30).unwrap()));
    assert!(dao.contains(Date::from_calendar_date(2022, Month::March, 28).unwrap()));
    assert!(!dao.contains(Date::from_calendar_date(2022, Month::March, 27).unwrap()));
    assert!(!dao.contains(Date::from_calendar_date(2022, Month::April, 1).unwrap()));
}

#[test]
fn readme_date_range() {
    use time::{Date, Month};

    // Is just a span between two dates
    let d1 = Date::from_calendar_date(2022, Month::January, 1).unwrap();
    let d2 = Date::from_calendar_date(2025, Month::March, 2).unwrap();
    let dr1 = DateRange::new(d1, d2);

    // Can be created from a date and a duration as well
    let d3 = Date::from_calendar_date(2021, Month::August, 15).unwrap();
    let dur = Duration::new(0, 0, 1); // 1 year
    let dr2 = DateRange::from_duration(d3, dur).unwrap();

    // Can be converted back into a duration
    assert_eq!(dr2.as_duration(), dur);

    // Can also be converted into days, weeks, months, quarters & years
    // Parameter is whther to count the part period at the end or not
    assert_eq!(dr1.as_days(), 1_156);
    assert_eq!(dr1.as_weeks(false), 165);
    assert_eq!(dr1.as_weeks(true), 166);
    assert_eq!(dr1.as_months(false), 38);
    assert_eq!(dr1.as_months(true), 39);
    assert_eq!(dr1.as_quarters(false), 12);
    assert_eq!(dr1.as_quarters(true), 13);
    assert_eq!(dr1.as_years(false), 3);
    assert_eq!(dr1.as_years(true), 4);

    // Can intersect or union two date ranges
    let mut dr3 = dr1.intersect(&dr2).unwrap();
    assert_eq!(dr3.as_days(), 226);
    dr3 = dr1.union(&dr2).unwrap();
    assert_eq!(dr3.as_days(), 1_295);

    // Can also test if a date is within the range
    let d4 = Date::from_calendar_date(2023, Month::July, 30).unwrap();
    assert!(dr1.contains(d4));
    assert!(!dr2.contains(d4));
}

#[test]
fn readme_timeline() {
    use time::{Date, Month};

    // Is a date range with periodicty
    let from = Date::from_calendar_date(2022, Month::January, 1).unwrap();
    let dur = Duration::new(0, 0, 10);
    let dr = DateRange::from_duration(from, dur).unwrap();
    let tlm = Timeline::new(dr, Period::Month); // Monthly timeline over 10 years

    // You can change periodicity
    let tld = tlm.change_periodicity(Period::Day);
    let tlw = tlm.change_periodicity(Period::Week);
    let tlq = tlm.change_periodicity(Period::Quarter);
    let tly = tlm.change_periodicity(Period::Year);

    // You can get the length of the timeline
    assert_eq!(tld.len(), 3_652);
    assert_eq!(tlw.len(), 522); // actually 521 weeks and 5 days but the short period counts
    assert_eq!(tlm.len(), 120);
    assert_eq!(tlq.len(), 40);
    assert_eq!(tly.len(), 10);

    // You can find the index at a given date
    let d = Date::from_calendar_date(2025, Month::July, 6).unwrap();
    assert_eq!(tld.index_at(d).unwrap(), 1_282);
    assert_eq!(tlw.index_at(d).unwrap(), 183);
    assert_eq!(tlm.index_at(d).unwrap(), 42);
    assert_eq!(tlq.index_at(d).unwrap(), 14);
    assert_eq!(tly.index_at(d).unwrap(), 3);

    // Or you can pull out a date range that covers the index
    let mut dr2 = tly.index(3).unwrap();
    let mut d = dr2.from();
    assert_eq!((d.year(), d.month() as u8, d.day()), (2025, 1, 1));
    d = dr2.to();
    assert_eq!((d.year(), d.month() as u8, d.day()), (2026, 1, 1));

    // you can even index in from the end
    dr2 = tlw.index(-5).unwrap();
    d = dr2.from();
    assert_eq!((d.year(), d.month() as u8, d.day()), (2031, 11, 29));
    d = dr2.to();
    assert_eq!((d.year(), d.month() as u8, d.day()), (2031, 12, 6));
}

#[test]
fn readme_timeseries() {
    use time::{Date, Month};

    // Finally, a time series is a timeline with a matching vector of values
    let from = Date::from_calendar_date(2022, Month::January, 1).unwrap();
    let dur = Duration::new(0, 0, 2); // 0 days, 0 months, 2 years i.e. 2 years
    let dr = DateRange::from_duration(from, dur).unwrap();
    let tl = Timeline::new(dr, Period::Quarter);
    let v1 = vec![1, 2, 3, 4, 5, 6, 7, 8];
    let ts1 = TimeSeries::new(&tl, v1).unwrap();

    // The length of the timeline and the values must match
    let v2 = vec![1, 2, 3, 4, 5, 6, 7];
    assert!(TimeSeries::new(&tl, v2.clone()).is_err());

    // You can extract values from a TS, either at a date ...
    let d = Date::from_calendar_date(2022, Month::December, 13).unwrap();
    assert_eq!(ts1.value(d), Some(&4));

    // ...or a slice reference over a date range
    let d = Date::from_calendar_date(2022, Month::April, 1).unwrap();
    let slice_dur = Duration::new(0, 9, 0);
    let slice_dr = DateRange::from_duration(d, slice_dur).unwrap();
    assert_eq!(ts1.value_range(slice_dr).unwrap(), vec![2, 3, 4]);

    // You can create a time series from a partial specification
    let mut ts3 = TimeSeries::new_partial(&tl, 0, &v2, 0);
    assert_eq!(ts3.value_range(dr).unwrap(), vec![1, 2, 3, 4, 5, 6, 7, 0]);

    // Partial creation will truncate overflowing values on the RHS as required
    ts3 = TimeSeries::new_partial(&tl, 3, &v2, 0);
    assert_eq!(ts3.value_range(dr).unwrap(), vec![0, 0, 0, 1, 2, 3, 4, 5]);

    // You can create a timeseries from a "generator function"
    // A generator function builds on the previous period's value
    let d2 = Date::from_calendar_date(2022, Month::July, 1).unwrap();
    let op = |t: DateRange, a: i32| -> i32 {
        if t.from() < d2 {
            a
        } else {
            a + 1
        }
    };
    let ts4 = TimeSeries::new_generator(&tl, 1, op);
    assert_eq!(ts4.value_range(dr).unwrap(), vec![1, 1, 2, 3, 4, 5, 6, 7]);

    // This is useful for building an indexation profile
    let indexation_factor: f64 = f64::powf(1.08, 0.25);
    let op = |_t: DateRange, a: f64| -> f64 { a * indexation_factor };
    let ts4_f = TimeSeries::new_generator(&tl, 1.0, op);
    let d3 = Date::from_calendar_date(2022, Month::October, 1).unwrap();
    let d4 = Date::from_calendar_date(2023, Month::December, 31).unwrap();
    assert!((ts4_f.value(d3).unwrap() - 1.08).abs() < 1e-5);
    assert!((ts4_f.value(d4).unwrap() - 1.1664).abs() < 1e-5);

    // You can shift a time series, in both directions
    let shift = Duration::new(0, 15, 0);
    let mut ts5 = ts1.shift(shift, 0).unwrap();
    assert_eq!(ts5.value_range(dr).unwrap(), vec![6, 7, 8, 0, 0, 0, 0, 0]);
    ts5 = ts1.shift(shift.invert(), 0).unwrap();
    assert_eq!(ts5.value_range(dr).unwrap(), vec![0, 0, 0, 0, 0, 1, 2, 3]);

    // You can cast the underlying values to float and int, where datatypes allow
    let ts6 = ts1.cast_f64();
    assert_eq!(
        ts6.value_range(dr).unwrap(),
        vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]
    );
    // This is still tbd as you can't get from f64 to i32 without making some lossy adjustments
    //let ts7 = ts6.cast_i32();
    //assert_eq!(ts7.value_range(dr).unwrap(), vec![1, 2, 3, 4, 5, 6, 7, 8]);

    // You can update values of a TimeSeries in place
    // Either with a straight replacement or you can add
    ts3.update((d, 100));
    assert_eq!(ts3.value_range(dr).unwrap(), vec![0, 100, 0, 1, 2, 3, 4, 5]);
    ts3.update_add((d, 200));
    assert_eq!(ts3.value_range(dr).unwrap(), vec![0, 300, 0, 1, 2, 3, 4, 5]);

    // You can change the periodicity of a TimeSeries
    // N.B. only works with f64 currently as you might need to split a period
    let tly = Timeline::new(dr, Period::Year);
    let ts8 = ts6.change_periodicity(&tly, &AggType::Add).unwrap();
    assert_eq!(ts8.value_range(dr).unwrap(), vec![10.0, 26.0]);

    // All of which is pre-amble to the real purpose of Time Series obejcts which is to combine them
    // Pair-wise combination is assumed

    // Standard primitive operators work
    let mut ts9 = (&ts1 + &ts3).unwrap();
    assert_eq!(
        ts9.value_range(dr).unwrap(),
        vec![1, 302, 3, 5, 7, 9, 11, 13]
    );
    ts9 = (&ts1 - &ts3).unwrap();
    assert_eq!(
        ts9.value_range(dr).unwrap(),
        vec![1, -298, 3, 3, 3, 3, 3, 3]
    );
    ts9 = (&ts1 * &ts3).unwrap();
    assert_eq!(
        ts9.value_range(dr).unwrap(),
        vec![0, 600, 0, 4, 10, 18, 28, 40]
    );

    // We can also write a generic function that can be pairwise applied to the elements of a TS
    let op = |(&a, &b)| {
        if a < 3 {
            1
        } else {
            b + 1
        }
    };
    let mut ts10 = fx!(op, &ts1, &ts3).unwrap();
    assert_eq!(ts10.value_range(dr).unwrap(), vec![1, 1, 1, 2, 3, 4, 5, 6]);

    // and we can pull the same trick, but additionally with reference to the timeline
    let date = Date::from_calendar_date(2023, Month::April, 1).unwrap();
    // Note: Need to declare the types of the input as the Rust compiler cannot 
    // infer types with this function
    let op = |(t, &a, &b): (DateRange, &i32, &i32)| {
        if t.contains(date) {
            1000
        } else if a < 3 {
            1
        } else {
            b + 1
        }
    };
    ts10 = fxt!(op, &ts1, &ts3).unwrap();
    assert_eq!(
        ts10.value_range(dr).unwrap(),
        vec![1, 1, 1, 2, 3, 1000, 5, 6]
    );

    // You can iterate through a TimeSeries
    // ... which means things like zip, map, fold etc will all work
    let q = Duration::new(0, 3, 0);
    for (i, (drp, val)) in ts1.iter().enumerate() {
        match i {
            0 => {
                let d = Date::from_calendar_date(2022, Month::January, 1).unwrap();
                assert_eq!(drp, DateRange::from_duration(d, q).unwrap());
                assert_eq!(val, &1);
            }
            2 => {
                let d = Date::from_calendar_date(2022, Month::July, 1).unwrap();
                assert_eq!(drp, DateRange::from_duration(d, q).unwrap());
                assert_eq!(val, &3);
            }
            7 => {
                let d = Date::from_calendar_date(2023, Month::October, 1).unwrap();
                assert_eq!(drp, DateRange::from_duration(d, q).unwrap());
                assert_eq!(val, &8);
            }
            _ => {}
        }
    }

    // There are also some utility functions defined on the the time series
    // These mimic Excel functionality
    // Only done SUM and SUMPRODUCT so far, but more to follow...
    assert_eq!(ts10.sum(), 1019);
    assert_eq!(ts3.sum_product(&ts1).unwrap(), 700)
}
