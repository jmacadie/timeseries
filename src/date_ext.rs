
trait DateExt {
    fn date_add(date: Date, count: i64, period: Period) -> Option<Date>;
    fn date_diff(date1: Date, date2: Date) -> Duration;
}