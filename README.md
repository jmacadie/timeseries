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
* Deploying solutions - If you've built a calculation engine it might be nice to deploy it somewhere so it can form part of an automated calculation pipeline, or spun up in many worker nodes to parallelise some calculation workload. This *can* be done with Excel but trust me it's a hassle
* Corruption - Excel files corrupt. You'll be working on a key file and then one day it's like "Nope ... just, nope". You better pray you have a recent uncorrupted version of the file knocking around because you're not using your head file again
* Code / algorithm re-use - I must have built about a million (counting is a modeller's specialist skillset) accounting corkscrews in Excel. In a coded language it should be possible to build a library version of these things and then use re-use the library version. Rust's use of generics and traits should be particularly useful for implementing this
* tbc...

## Rust Inspiration

This library is built using as few external crates as possible and if at all possible I've tried to remove any code that could panic. This will be an ongoing objective for this library.

The one crate I do build on pretty extensively is [Time](https://crates.io/crates/time). I also looked at [Chrono](https://crates.io/crates/chrono) but it looks like that's not being updated any more, plus Time seemed to have everything I wanted already. Where Time drops off is considering durations of greater than a week, owing to the fact that months can be a variable number of days long. I have spent quite some time grappling with these difficulties as financial models typically are built at the month or greater resolution. My (current) solution to these difficulties is contained within the Duration object within this library

---

## How to Use

```rust
// Create a timeline
let from = Date::from_calendar_date(2022, Month::January, 1).unwrap();
let dur = Duration::new(0, 0, 2); // days, months, years
let dr = DateRange::from_duration(from, dur).unwrap();
let tl = Timeline::new(dr, Period::Quarter);

// Create two timeseries
let v1 = vec![1, 2, 3, 4, 5, 6, 7, 8];
let ts1 = TimeSeries::new(&tl, v1).unwrap();
let v2 = vec![5, 6, 7, 8, -10, 0, -11, 0];
let ts2 = TimeSeries::new(&tl, v2).unwrap();

// Write a generic function that can be pairwise applied to the elements of a TS and check OK
let op = |(&a, &b): (&i32, &i32)| -> i32 {
    if a < 3 {
        1
    } else {
        b + 1
    }
};
let ts3 = ts1.apply(&ts2, op).unwrap();
assert_eq!(ts3.values, vec![1, 1, 8, 9, -9, 1, -10, 1]);

// Apply a shift
let shift = Duration::new(0, -9, 0); // days, months, years
let ts4 = ts3.shift(shift, 0).unwrap();
assert_eq!(ts4.values, vec![0, 0, 0, 1, 1, 8, 9, -9]);
```

To be extensively expanded upon...

## Stuff that needs doing

In no particular order:

* Import data from various sources (CSV, Excel etc)
* Output model results, to CSV at first, if nothing else
* Output charts
* Think about how to debug a model - naive implementation would be to build a grid view of outputs, like Excel, but is there a different way to achieve the same end goal?
* Apply TS combinations to more than just two source TS objects, an Excel formula can reference any number of dependents. I think this is going to need a macro given the potentially variable number of inputs
* Generator style TS that build on the previous period's values (e.g. indeaxtion formulae)
* Change Periodicity needs work - can it be extended beyond f64? Should it be applied to other aggregation methods than Add?
* Errors are super duff. No idea what I'm doing here but these should definitely be re-worked
* Documentation about how to use every part of this library
* Put this on crates.io?

---

### License

TimeSeries is licensed under the <a href="LICENSE">MIT License</a>. I'm open to using other licenses, whatever makes this freely available
