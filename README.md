# TimeSeries

TimeSeries is a framework for building analytical models in Rust that have a time dimension.

---

## Inspiration

The inspiration for writing this is to replace [financial models that would traditionally be built in Excel](https://en.wikipedia.org/wiki/Financial_modeling). The [Corporate Finance Institute](https://corporatefinanceinstitute.com/resources/knowledge/modeling/what-is-financial-modeling/) gives a decent explanation of process of writing such a model and the broad scope, although the whole area is very subjective & I don't agree with everything they've written!

Excel, or spreadsheet software in general, has many advantages that explain it's ubiquity when it comes to building financial models. These advantages will need to be replicated, surpassed or obviated for any replacement system to be viable:

* Both the calculations and the value results of the intermediate calculation steps are visible - when there are thousands of rows of calculations being able to quickly see where numbers look right and where they look wrong is very important
* Ability to import data in from a variety of sources - Excel, CSV, databases, text files etc.
* Ability to output the results of the model to other users including:
   * Tables of values (including output statements such as cash flows)
   * Charts
   * Dashboards (including making available certain key inputs to sensitise the output)
   * Formatting of said outputs so they're easy to read
   * Using an output format other users can generally access - i.e. most business users have a copy of Excel on their laptop
* Built-in function support - personally I find this one a little debatable and, within reason, I'd rather build most functions myself using primitive operators {+, -, /, *, ^} rather than rely on Excel's black-box implementation. For example, are all users of an NPV function really aware of Excel's inherent timing assumptions?
* Formula auditing - being able to see what a formula depends on and chase the calculation back up the chain to find root problems is an essential part of building a financial model
* Excel is pretty quick - if you're not careful a coded solution (esp. in something like Python) can be slower than just building the thing in Excel

However, all is not sweetness & light in the garden of Excel financial models, or I wouldn't be building this! Some downsides to Excel are:

* Source control - all Excel models I've ever seen rely on file management to control versioning, which means having a version number in the file name and storing old versions of the file in some sort of archive folder. Also Excel models don't work with git (or other versioning software) so unless you invest in [onerous stand-alone options](https://www.operis.com/excel-add-ins/) (& use them!) you never really know what's changed in any two Excel file versions
* Testing - you can do this in Excel and every authority in this domain I know says it's really important but the honest truth is that most Excel models aren't tested that well. Things like test suites and code coverage tools would be very useful to address this deficiency
* Speed - I know, I listed this as an upside, but if pushed hard enough Excel can get slow enough to be a problem. Coding in Rust should give us a head start on these sorts of issues
* Data size - it's reasonably well known that Excel suffers if you try to use it with too much data. These issues ought to be more easily dealt with in code, not given that much thought to this as yet
* Deploying solutions - If you've built a calculation engine it might be nice to deploy it somewhere so it can form part of an automated calculation pipeline, or spun up in many worker nodes to parallelise some calculation workload. This *can* be done with Excel but trust me it's a hassle
* Corruption - Excel files corrupt. You'll be working on a key file and then one day it's like "Nope ... just, nope". You better pray you have a recent uncorrupted version of the file knocking around because you're not using your head file again
* Code / algorithm re-use - I must have built about a million (counting is a modeller's specialist skillset) accounting corkscrews in Excel. In a coded language it should be possible to build a library version of these things and then use re-use the library version. Rust's use of generics and traits should be particularly useful for implementing this
* tbc...

## Rust Inspiration

This library is built using as few external crates as possible and if at all possible I've tried to remove any code that could panic. This will be an ongoing objective for this library.

The one crate I do build on pretty extensively is [Time](https://crates.io/crates/time). I also looked at [Chrono](https://crates.io/crates/chrono) but it looks like that's not being updated any more, plus Time seemed to have everything I wanted already. Where Time drops off is considering durations of greater than a week, owing to the fact that months can be a variable number of days long. I have spent quite some time grappling with these difficulties as financial models typically are built at the month or greater resolution. My (current) solution to these difficulties is contained within the Duration object within this library

---

## How to Use

### Duration

```rust
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
```

### Date Range
```rust
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
```

### Timeline
```rust
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
assert_eq!(tlw.len(), 522); // actually 521 weeks and 5 days, but the short period counts
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
```

### Time Series

```rust
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
let mut ts3 = TimeSeries::new_partial(&tl, 0, v2.clone(), 0);
assert_eq!(ts3.value_range(dr).unwrap(), vec![1, 2, 3, 4, 5, 6, 7, 0]);

// Partial creation will truncate overflowing values on the RHS as required
ts3 = TimeSeries::new_partial(&tl, 3, v2, 0);
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

// We can also Write a generic function that can be pairwise applied to the elements of a TS
let op = |(&a, &b): (&i32, &i32)| -> i32 {
    if a < 3 {
        1
    } else {
        b + 1
    }
};
let mut ts10 = ts1.apply(&ts3, op).unwrap();
assert_eq!(ts10.value_range(dr).unwrap(), vec![1, 1, 1, 2, 3, 4, 5, 6]);

// and we can pull the same trick, but additionally with reference to the timeline
let date = Date::from_calendar_date(2023, Month::April, 1).unwrap();
let op = |(t, &a, &b): (DateRange, &i32, &i32)| -> i32 {
    if t.contains(date) {
        1000
    } else if a < 3 {
        1
    } else {
        b + 1
    }
};
ts10 = ts1.apply_with_time(&ts3, op).unwrap();
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
```

## Stuff that needs doing

In no particular order:

* Import data from various sources (CSV, Excel etc)
* Output model results, to CSV at first, if nothing else
* Output charts
* Think about how to debug a model - naive implementation would be to build a grid view of outputs, like Excel, but is there a different way to achieve the same end goal? Can we use something like Yew to output an interactive view on the calculations, rendered as a webpage?
* Apply TS combinations to more than just two source TS objects, an Excel formula can reference any number of dependents. I think this is going to need a macro given the potentially variable number of inputs
* Change Periodicity needs work - can it be extended beyond f64? Should it be applied to other aggregation methods than Add?
* Errors are super duff. No idea what I'm doing here but these should definitely be re-worked
* Documentation about how to use every part of this library. I have now put faily decent code examples up on this page but it now feels like too much here. Should I create a booK?
* Put this on crates.io?

---

### License

TimeSeries is licensed under the <a href="LICENSE">MIT License</a>. I'm open to using other licenses, whatever makes this freely available
