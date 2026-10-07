//! Time instants of `xsd:dateTime` and `xsd:dateTimeStamp` (XML Schema 1.1
//! Part 2 §3.3.7 and §3.4.28): the lexical forms
//! `-?([1-9][0-9]{3,}|0[0-9]{3})-MM-DDThh:mm:ss(\.[0-9]+)?` and the end of the
//! day `24:00:00(\.0+)?`, with an optional time zone `Z` or `(+|-)hh:mm` of at
//! most fourteen hours, read into the values of the seven-property model
//! (§D.2.1). An `xsd:dateTimeStamp` needs the time zone.
//!
//! A value keeps the date and the time as written, with the time zone offset:
//! OWL 2 (Structural Specification §4.7) counts two values of one instant at
//! different offsets as different. The day must exist in its month (the
//! proleptic Gregorian calendar, in which year zero is a leap year), and
//! `24:00:00` is the first instant of the next day.
#![allow(
    clippy::ptr_arg,
    clippy::manual_range_contains,
    clippy::manual_is_multiple_of,
    clippy::manual_map,
    clippy::len_zero,
    clippy::redundant_pattern_matching
)] // Indexed operations and explicit branches for the pinned extraction subset.

use crate::datatypes::{DataValue, Moment};
use crate::numbers::{add_naturals, subtract_naturals};

pub(crate) fn is_digit(byte: u8) -> bool {
    (48 <= byte) & (byte <= 57)
}
/// The end of the digits of `bytes` from `index` on.
pub(crate) fn digits_end(bytes: &Vec<u8>, index: usize) -> usize {
    if index < bytes.len() {
        if is_digit(bytes[index]) {
            digits_end(bytes, index + 1)
        } else {
            index
        }
    } else {
        index
    }
}
/// The number that the two bytes at `index` write, if they are digits.
fn two_digits(bytes: &Vec<u8>, index: usize) -> Option<u8> {
    if (index < bytes.len()) && (1 < bytes.len() - index) {
        if is_digit(bytes[index]) & is_digit(bytes[index + 1]) {
            Some((bytes[index] - 48) * 10 + (bytes[index + 1] - 48))
        } else {
            None
        }
    } else {
        None
    }
}
/// Whether the digits `bytes[start..end]` are a year: four digits, or more
/// without a leading zero.
fn year_shaped(bytes: &Vec<u8>, start: usize, end: usize) -> bool {
    if (start < end) & (end <= bytes.len()) {
        if end - start == 4 {
            true
        } else if 4 < end - start {
            bytes[start] != 48
        } else {
            false
        }
    } else {
        false
    }
}
/// The first index of `bytes[index..end]` whose byte is not `0`, or `end`.
fn nonzero_start(bytes: &Vec<u8>, index: usize, end: usize) -> usize {
    if (index < end) & (end <= bytes.len()) {
        if bytes[index] == 48 {
            nonzero_start(bytes, index + 1, end)
        } else {
            index
        }
    } else {
        index
    }
}
/// The end of `bytes[start..end]` without its trailing `0`s.
pub(crate) fn trimmed_end(bytes: &Vec<u8>, start: usize, end: usize) -> usize {
    if (start < end) & (end <= bytes.len()) {
        if bytes[end - 1] == 48 {
            trimmed_end(bytes, start, end - 1)
        } else {
            end
        }
    } else {
        end
    }
}
/// `out` followed by `bytes[index..end]`.
pub(crate) fn copy_span(bytes: &Vec<u8>, index: usize, end: usize, mut out: Vec<u8>) -> Vec<u8> {
    if (index < end) & (end <= bytes.len()) {
        if out.len() < usize::MAX {
            out.push(bytes[index]);
        }
        copy_span(bytes, index + 1, end, out)
    } else {
        out
    }
}
/// The digit `index` places from the right of the digits, and 0 beyond them.
fn digit_at(digits: &Vec<u8>, index: usize) -> u8 {
    if index < digits.len() {
        let byte = digits[digits.len() - 1 - index];
        if is_digit(byte) {
            byte - 48
        } else {
            0
        }
    } else {
        0
    }
}
/// The number that the digits `places` and `places + 1` places from the right
/// of the digits write.
fn pair_at(digits: &Vec<u8>, places: usize) -> u8 {
    if places < usize::MAX {
        digit_at(digits, places + 1) * 10 + digit_at(digits, places)
    } else {
        0
    }
}
/// Whether the year with the digits `year` is a leap year: a multiple of 400,
/// or of 4 but not of 100. The sign does not matter.
fn leap(year: &Vec<u8>) -> bool {
    let low = pair_at(year, 0);
    if low == 0 {
        pair_at(year, 2) % 4 == 0
    } else {
        low % 4 == 0
    }
}
/// The number of days of the month in the year with the digits `year`.
fn month_days(year: &Vec<u8>, month: u8) -> u8 {
    if month == 2 {
        if leap(year) {
            29
        } else {
            28
        }
    } else if (month == 4) | (month == 6) | (month == 9) | (month == 11) {
        30
    } else {
        31
    }
}
/// The date `-MM-DD` at `index` of a year with the digits `year`: its month
/// and its day, if the day is in the month.
fn date_at(lexical: &Vec<u8>, index: usize, year: &Vec<u8>) -> Option<(u8, u8)> {
    if (index < lexical.len()) && (5 < lexical.len() - index) {
        if (lexical[index] == 45) & (lexical[index + 3] == 45) {
            match two_digits(lexical, index + 1) {
                Some(month) => match two_digits(lexical, index + 4) {
                    Some(day) => {
                        if (1 <= month)
                            & (month <= 12)
                            & (1 <= day)
                            & (day <= month_days(year, month))
                        {
                            Some((month, day))
                        } else {
                            None
                        }
                    }
                    None => None,
                },
                None => None,
            }
        } else {
            None
        }
    } else {
        None
    }
}
/// The time `Thh:mm:ss` at `index`: its hour, minute and whole seconds, as
/// written.
fn time_at(lexical: &Vec<u8>, index: usize) -> Option<(u8, u8, u8)> {
    if (index < lexical.len()) && (8 < lexical.len() - index) {
        if (lexical[index] == 84) & (lexical[index + 3] == 58) & (lexical[index + 6] == 58) {
            match two_digits(lexical, index + 1) {
                Some(hour) => match two_digits(lexical, index + 4) {
                    Some(minute) => match two_digits(lexical, index + 7) {
                        Some(second) => Some((hour, minute, second)),
                        None => None,
                    },
                    None => None,
                },
                None => None,
            }
        } else {
            None
        }
    } else {
        None
    }
}
/// The end of the fraction of a second from `index` on: `index` without a
/// `.`, the end of the digits after one, and `None` for a `.` without digits.
fn fraction_end(lexical: &Vec<u8>, index: usize) -> Option<usize> {
    if index < lexical.len() {
        if lexical[index] == 46 {
            let stop = digits_end(lexical, index + 1);
            if index + 1 < stop {
                Some(stop)
            } else {
                None
            }
        } else {
            Some(index)
        }
    } else {
        Some(index)
    }
}
/// The time zone that `lexical[index..]` writes: `Some(None)` for none at the
/// end, and for `Z` or `(+|-)hh:mm` of at most fourteen hours whether it is
/// west of UTC, its hours and its minutes, an offset of zero not west.
fn zone_value(lexical: &Vec<u8>, index: usize) -> Option<Option<(bool, u8, u8)>> {
    if index < lexical.len() {
        let rest = lexical.len() - index;
        if (lexical[index] == 90) & (rest == 1) {
            Some(Some((false, 0, 0)))
        } else if ((lexical[index] == 43) | (lexical[index] == 45)) & (rest == 6) {
            if lexical[index + 3] == 58 {
                zone_parts(
                    lexical[index] == 45,
                    two_digits(lexical, index + 1),
                    two_digits(lexical, index + 4),
                )
            } else {
                None
            }
        } else {
            None
        }
    } else {
        Some(None)
    }
}
/// The time zone with the sign, hours and minutes, if they are within fourteen
/// hours.
fn zone_parts(
    west: bool,
    hours: Option<u8>,
    minutes: Option<u8>,
) -> Option<Option<(bool, u8, u8)>> {
    match hours {
        Some(hours) => match minutes {
            Some(minutes) => {
                if ((hours <= 13) & (minutes <= 59)) | ((hours == 14) & (minutes == 0)) {
                    Some(Some((
                        west & ((hours != 0) | (minutes != 0)),
                        hours,
                        minutes,
                    )))
                } else {
                    None
                }
            }
            None => None,
        },
        None => None,
    }
}
/// The digits and the sign of the year after a year: one less in size for a
/// negative year.
fn next_year(negative: bool, year: &Vec<u8>) -> (bool, Vec<u8>) {
    let mut one = Vec::new();
    one.push(49);
    if negative {
        let rest = subtract_naturals(year, &one);
        (0 < rest.len(), rest)
    } else {
        (false, add_naturals(year, &one))
    }
}
/// The first instant of the day after the moment's day.
fn next_day(moment: Moment) -> Moment {
    if moment.day < month_days(&moment.year, moment.month) {
        Moment {
            day: moment.day + 1,
            hour: 0,
            ..moment
        }
    } else if moment.month < 12 {
        Moment {
            month: moment.month + 1,
            day: 1,
            hour: 0,
            ..moment
        }
    } else {
        let (negative, year) = next_year(moment.negative, &moment.year);
        Moment {
            negative,
            year,
            month: 1,
            day: 1,
            hour: 0,
            ..moment
        }
    }
}
/// The value of a moment as written: itself when its time is on the clock,
/// the first instant of the next day for `24:00:00`, and `None` otherwise.
fn settled(moment: Moment) -> Option<DataValue> {
    if moment.hour < 24 {
        if (moment.minute < 60) & (moment.second < 60) {
            Some(DataValue::Moment(moment))
        } else {
            None
        }
    } else if (moment.hour == 24)
        & (moment.minute == 0)
        & (moment.second == 0)
        & (moment.fraction.len() == 0)
    {
        Some(DataValue::Moment(next_day(moment)))
    } else {
        None
    }
}
/// Whether there is no time zone.
fn no_zone(zone: &Option<(bool, u8, u8)>) -> bool {
    match zone {
        Some(_) => false,
        None => true,
    }
}
/// The digits of the fraction of a second `lexical[start..stop]` after its
/// `.`, without trailing zeros, where `start` is the place of the `.`.
fn fraction_digits(lexical: &Vec<u8>, start: usize, stop: usize) -> Vec<u8> {
    if (start < stop) & (stop <= lexical.len()) {
        copy_span(
            lexical,
            start + 1,
            trimmed_end(lexical, start + 1, stop),
            Vec::new(),
        )
    } else {
        Vec::new()
    }
}
/// The value of a lexical form whose year is `lexical[start..end]` and whose
/// date and time take the 15 bytes from `end` on.
fn moment_after(
    lexical: &Vec<u8>,
    negative: bool,
    start: usize,
    end: usize,
    stamped: bool,
) -> Option<DataValue> {
    let year = copy_span(lexical, nonzero_start(lexical, start, end), end, Vec::new());
    let negative = negative & (0 < year.len());
    match date_at(lexical, end, &year) {
        Some((month, day)) => match time_at(lexical, end + 6) {
            Some((hour, minute, second)) => match fraction_end(lexical, end + 15) {
                Some(stop) => match zone_value(lexical, stop) {
                    Some(zone) => {
                        if stamped & no_zone(&zone) {
                            None
                        } else {
                            settled(Moment {
                                negative,
                                year,
                                month,
                                day,
                                hour,
                                minute,
                                second,
                                fraction: fraction_digits(lexical, end + 15, stop),
                                zone,
                            })
                        }
                    }
                    None => None,
                },
                None => None,
            },
            None => None,
        },
        None => None,
    }
}
/// The value of a lexical form of `xsd:dateTime`, or of `xsd:dateTimeStamp`
/// when `stamped`, if it is in the lexical space and short enough for the
/// arithmetic on its year.
pub fn moment_value(lexical: &Vec<u8>, stamped: bool) -> Option<DataValue> {
    if lexical.len() < usize::MAX / 16 {
        let negative = (0 < lexical.len()) && (lexical[0] == 45);
        let start = if negative { 1 } else { 0 };
        let end = digits_end(lexical, start);
        if year_shaped(lexical, start, end) {
            if 15 <= lexical.len() - end {
                moment_after(lexical, negative, start, end, stamped)
            } else {
                None
            }
        } else {
            None
        }
    } else {
        None
    }
}
