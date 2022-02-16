#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Period {
    Day = 1,
    Week = 7,
    Month = 30,
    Quarter = 91,
    Year = 365,
}
