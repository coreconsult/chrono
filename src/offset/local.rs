// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! The local (system) time zone.

use oldtime;
// TODO(timvisee): use this?
use oldtime::Duration as Timespec;

use super::fixed::FixedOffset;
use super::{LocalResult, TimeZone};
use naive::{NaiveDate, NaiveDateTime, NaiveTime};
use Timelike;
use {Date, DateTime};

/// Converts a `time::OffsetDateTime` struct into the timezone-aware `DateTime`.
/// This assumes that `time` is working correctly, i.e. any error is fatal.
// TODO(timvisee): correct offset logic?
fn offsetdatetime_to_datetime(odt: oldtime::OffsetDateTime) -> DateTime<Local> {
    let date = NaiveDate::from_ymd(odt.year(), odt.month() as u32, odt.day() as u32);
    let time = NaiveTime::from_hms_nano(
        odt.hour() as u32,
        odt.minute() as u32,
        odt.second() as u32,
        odt.nanosecond(),
    );
    let offset = FixedOffset::east(odt.offset().as_seconds());
    DateTime::from_utc(date.and_time(time) - offset, offset)
}

/// Converts a local `NaiveDateTime` to the `time::Timespec`.
fn datetime_to_timespec(d: &NaiveDateTime, local: bool) -> Timespec {
    let offset = if local {
        oldtime::UtcOffset::try_current_local_offset()
            .unwrap_or(oldtime::UtcOffset::UTC)
            .as_seconds() as i64
    } else {
        0
    };

    // do not set nanoseconds, OS APIs are heavily inconsistent in terms of leap second handling
    Timespec::new(d.timestamp() + offset, 0)
}

/// The local timescale. This is implemented via the standard `time` crate.
///
/// Using the [`TimeZone`](./trait.TimeZone.html) methods
/// on the Local struct is the preferred way to construct `DateTime<Local>`
/// instances.
///
/// # Example
///
/// ~~~~
/// use chrono::{Local, DateTime, TimeZone};
///
/// let dt: DateTime<Local> = Local::now();
/// let dt: DateTime<Local> = Local.timestamp(0, 0);
/// ~~~~
#[derive(Copy, Clone, Debug)]
pub struct Local;

impl Local {
    /// Returns a `Date` which corresponds to the current date.
    pub fn today() -> Date<Local> {
        Local::now().date()
    }

    /// Returns a `DateTime` which corresponds to the current date.
    #[cfg(not(all(target_arch = "wasm32", not(target_os = "wasi"), feature = "wasmbind")))]
    pub fn now() -> DateTime<Local> {
        offsetdatetime_to_datetime(oldtime::OffsetDateTime::now_utc())
    }

    /// Returns a `DateTime` which corresponds to the current date.
    #[cfg(all(target_arch = "wasm32", not(target_os = "wasi"), feature = "wasmbind"))]
    pub fn now() -> DateTime<Local> {
        use super::Utc;
        let now: DateTime<Utc> = super::Utc::now();

        // Workaround missing timezone logic in `time` crate
        let offset = FixedOffset::west((js_sys::Date::new_0().get_timezone_offset() as i32) * 60);
        DateTime::from_utc(now.naive_utc(), offset)
    }
}

impl TimeZone for Local {
    type Offset = FixedOffset;

    fn from_offset(_offset: &FixedOffset) -> Local {
        Local
    }

    // they are easier to define in terms of the finished date and time unlike other offsets
    fn offset_from_local_date(&self, local: &NaiveDate) -> LocalResult<FixedOffset> {
        self.from_local_date(local).map(|date| *date.offset())
    }

    fn offset_from_local_datetime(&self, local: &NaiveDateTime) -> LocalResult<FixedOffset> {
        self.from_local_datetime(local).map(|datetime| *datetime.offset())
    }

    fn offset_from_utc_date(&self, utc: &NaiveDate) -> FixedOffset {
        *self.from_utc_date(utc).offset()
    }

    fn offset_from_utc_datetime(&self, utc: &NaiveDateTime) -> FixedOffset {
        *self.from_utc_datetime(utc).offset()
    }

    // override them for avoiding redundant works
    fn from_local_date(&self, local: &NaiveDate) -> LocalResult<Date<Local>> {
        // this sounds very strange, but required for keeping `TimeZone::ymd` sane.
        // in the other words, we use the offset at the local midnight
        // but keep the actual date unaltered (much like `FixedOffset`).
        let midnight = self.from_local_datetime(&local.and_hms(0, 0, 0));
        midnight.map(|datetime| Date::from_utc(*local, *datetime.offset()))
    }

    fn from_local_datetime(&self, local: &NaiveDateTime) -> LocalResult<DateTime<Local>> {
        let timespec = datetime_to_timespec(local, true);
        let offset =
            oldtime::UtcOffset::try_current_local_offset().unwrap_or(oldtime::UtcOffset::UTC);

        // datetime_to_timespec completely ignores leap seconds, so we need to adjust for them
        let mut datetime = oldtime::OffsetDateTime::from_unix_timestamp(timespec.whole_seconds());
        assert_eq!(datetime.nanosecond(), 0);
        datetime += Timespec::new(offset.as_seconds() as i64, local.nanosecond() as i32);

        LocalResult::Single(offsetdatetime_to_datetime(datetime))
    }

    fn from_utc_date(&self, utc: &NaiveDate) -> Date<Local> {
        let midnight = self.from_utc_datetime(&utc.and_hms(0, 0, 0));
        Date::from_utc(*utc, *midnight.offset())
    }

    #[cfg(all(target_arch = "wasm32", not(target_os = "wasi"), feature = "wasmbind"))]
    fn from_utc_datetime(&self, utc: &NaiveDateTime) -> DateTime<Local> {
        // Get the offset from the js runtime
        let offset = FixedOffset::west((js_sys::Date::new_0().get_timezone_offset() as i32) * 60);
        DateTime::from_utc(*utc, offset)
    }

    #[cfg(not(all(target_arch = "wasm32", not(target_os = "wasi"), feature = "wasmbind")))]
    fn from_utc_datetime(&self, utc: &NaiveDateTime) -> DateTime<Local> {
        let timespec = datetime_to_timespec(utc, false);

        // datetime_to_timespec completely ignores leap seconds, so we need to adjust for them
        let mut datetime = oldtime::OffsetDateTime::from_unix_timestamp(timespec.whole_seconds());
        assert_eq!(datetime.nanosecond(), 0);
        datetime += Timespec::new(0, utc.nanosecond() as i32);

        offsetdatetime_to_datetime(datetime)
    }
}

#[cfg(test)]
mod tests {
    use super::Local;
    use offset::TimeZone;
    use Datelike;

    #[test]
    fn test_local_date_sanity_check() {
        // issue #27
        assert_eq!(Local.ymd(2999, 12, 28).day(), 28);
    }

    #[test]
    fn test_leap_second() {
        // issue #123
        let today = Local::today();

        let dt = today.and_hms_milli(1, 2, 59, 1000);
        let timestr = dt.time().to_string();
        // the OS API may or may not support the leap second,
        // but there are only two sensible options.
        assert!(timestr == "01:02:60" || timestr == "01:03:00", "unexpected timestr {:?}", timestr);

        let dt = today.and_hms_milli(1, 2, 3, 1234);
        let timestr = dt.time().to_string();
        assert!(
            timestr == "01:02:03.234" || timestr == "01:02:04.234",
            "unexpected timestr {:?}",
            timestr
        );
    }
}
