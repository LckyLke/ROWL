import Rowl.Moments
import Mathlib.Data.Int.Interval

/-!
The order of time instants (XML Schema 1.1 Part 2 §D.2.1 and §E.3.4) and the
kernel's instants. The place of a moment on the time line (`Moment.key`) is
86400 seconds for each day before its date (`dayNumber`), which grows by one
from each date to the next (`dayNumber_next`), plus its time of the day less
its time zone offset; so among moments of one offset the places follow the
dates and times one after the other (`key_lt_iff`), and a place and an offset
fix the moment (`key_injective`). A moment moved by some minutes on the clock
(`shiftBy`) moves its place by as many minutes (`key_shiftBy`). There are
exactly 1681 moments with a time zone at an instant, one for each offset from
-14:00 to +14:00 (`zoned_at_card`), and one without (`unzoned_at`).

The kernel moves a moment on the clock (`moments.shifted`, `shifted_spec`), puts
a moment at its instant, at UTC for one with a time zone
(`moments.instant`, `instant_spec`), and compares two instants by their dates
and times one after the other (`moments.instant_order`, `instant_order_spec`).
-/
namespace Rowl.TimeOrder
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.DatatypeMap
open Rowl.Moments (momentOf CanonicalMoment DateOk)
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

/-! ### Days -/

/-- A date of the proleptic Gregorian calendar. -/
def DateValid (year : ℤ) (month day : ℕ) : Prop := 1 ≤ month ∧ month ≤ 12 ∧ 1 ≤ day ∧ day ≤ daysIn year month

/-- The days before a date, from the first of January of year 1 on. -/
def dayNumber (year : ℤ) (month day : ℕ) : ℤ :=
  365 * (year - 1) + ((year - 1) / 400 - (year - 1) / 100 + (year - 1) / 4) + (daysBefore year month : ℤ) +
    ((day : ℤ) - 1)

/-- The day before a date. -/
def prevDate (year : ℤ) (month day : ℕ) : ℤ × ℕ × ℕ :=
  if 1 < day then (year, month, day - 1)
  else if 1 < month then (year, month - 1, daysIn year (month - 1)) else (year - 1, 12, 31)

theorem daysBefore_one (year : ℤ) : daysBefore year 1 = 0 := rfl

theorem daysBefore_succ (year : ℤ) {month : ℕ} (h : 1 ≤ month) :
    daysBefore year (month + 1) = daysBefore year month + daysIn year month := by
  unfold daysBefore
  obtain ⟨k, rfl⟩ : ∃ k, month = k + 1 := ⟨month - 1, by omega⟩
  simp [List.range_succ]

theorem daysIn_bounds (year : ℤ) (month : ℕ) : 28 ≤ daysIn year month ∧ daysIn year month ≤ 31 :=
  Rowl.Moments.daysIn_le year month

/-- The days of the twelve months of a year. -/
theorem daysBefore_thirteen (year : ℤ) :
    (daysBefore year 13 : ℤ) = 365 + (if leapYear year then 1 else 0) := by
  unfold daysBefore
  simp [List.range_succ, daysIn]
  split <;> simp

theorem daysBefore_twelve (year : ℤ) : daysBefore year 12 + 31 = daysBefore year 13 := by
  rw [show daysBefore year 13 = daysBefore year 12 + daysIn year 12 from daysBefore_succ year (by norm_num)]
  simp [daysIn]

/-- The leap days before the year after `year` less those before `year`: one
    in a leap year. -/
theorem leap_days (year : ℤ) :
    (year / 400 - year / 100 + year / 4) - ((year - 1) / 400 - (year - 1) / 100 + (year - 1) / 4) =
      if leapYear year then 1 else 0 := by
  unfold leapYear
  by_cases h400 : year % 400 = 0
  · simp [h400]
    omega
  · by_cases h4 : year % 4 = 0
    · by_cases h100 : year % 100 = 0
      · simp [h400, h4, h100]
        omega
      · simp [h400, h4, h100]
        omega
    · simp [h400, h4]
      omega

theorem dayNumber_next {year : ℤ} {month day : ℕ} (valid : DateValid year month day) :
    dayNumber (nextDate year month day).1 (nextDate year month day).2.1 (nextDate year month day).2.2 =
      dayNumber year month day + 1 := by
  obtain ⟨m1, m12, d1, dIn⟩ := valid
  unfold nextDate
  split_ifs with h1 h2
  · simp only [dayNumber]; push_cast; ring
  · have := daysBefore_succ year m1
    simp only [dayNumber]
    rw [this]
    have : day = daysIn year month := by omega
    subst this
    push_cast; ring
  · have m : month = 12 := by omega
    subst m
    have d31 : daysIn year 12 = 31 := by simp [daysIn]
    have d : day = 31 := by omega
    subst d
    have total := daysBefore_thirteen year
    have twelve := daysBefore_twelve year
    have leaps := leap_days year
    simp only [dayNumber, daysBefore_one, add_sub_cancel_right]
    push_cast
    split_ifs at total leaps <;> omega

theorem nextDate_date_valid {year : ℤ} {month day : ℕ} (valid : DateValid year month day) :
    DateValid (nextDate year month day).1 (nextDate year month day).2.1 (nextDate year month day).2.2 := by
  obtain ⟨m1, m12, d1, dIn⟩ := valid
  have b := daysIn_bounds
  unfold nextDate
  split_ifs with h1 h2 <;> dsimp only
  · exact ⟨m1, m12, by omega, by omega⟩
  · exact ⟨by omega, by omega, le_rfl, by have := b year (month + 1); omega⟩
  · exact ⟨le_rfl, by omega, le_rfl, by have := b (year + 1) 1; omega⟩

theorem prevDate_valid {year : ℤ} {month day : ℕ} (valid : DateValid year month day) :
    DateValid (prevDate year month day).1 (prevDate year month day).2.1 (prevDate year month day).2.2 := by
  obtain ⟨m1, m12, d1, dIn⟩ := valid
  have b := daysIn_bounds
  unfold prevDate
  split_ifs with h1 h2 <;> dsimp only
  · exact ⟨m1, m12, by omega, by omega⟩
  · exact ⟨by omega, by omega, by have := b year (month - 1); omega, le_rfl⟩
  · exact ⟨by omega, le_rfl, by omega, by simp [daysIn]⟩

theorem next_prevDate {year : ℤ} {month day : ℕ} (valid : DateValid year month day) :
    nextDate (prevDate year month day).1 (prevDate year month day).2.1 (prevDate year month day).2.2 =
      (year, month, day) := by
  obtain ⟨m1, m12, d1, dIn⟩ := valid
  unfold prevDate
  split_ifs with h1 h2
  · simp only [nextDate]
    rw [if_pos (by omega)]
    simp; omega
  · have dIs : day = 1 := by omega
    subst dIs
    simp only [nextDate]
    rw [if_neg (by omega), if_pos (by omega)]
    simp; omega
  · have dIs : day = 1 := by omega
    have mIs : month = 1 := by omega
    subst dIs mIs
    simp [nextDate, daysIn]

theorem dayNumber_prev {year : ℤ} {month day : ℕ} (valid : DateValid year month day) :
    dayNumber (prevDate year month day).1 (prevDate year month day).2.1 (prevDate year month day).2.2 =
      dayNumber year month day - 1 := by
  have := dayNumber_next (prevDate_valid valid)
  rw [next_prevDate valid] at this
  dsimp only at this
  omega

/-- The days before the first of January of a year grow with the year. -/
theorem dayNumber_new_year_le {year year' : ℤ} (le : year ≤ year') : dayNumber year 1 1 ≤ dayNumber year' 1 1 := by
  simp only [dayNumber, daysBefore_one]
  omega

theorem daysBefore_add {year : ℤ} {month : ℕ} (h : 1 ≤ month) (k : ℕ) :
    daysBefore year month + k * 28 ≤ daysBefore year (month + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show month + (k + 1) = month + k + 1 by omega, daysBefore_succ year (by omega)]
    have := (daysIn_bounds year (month + k)).1
    nlinarith

theorem daysBefore_mono {year : ℤ} {month month' : ℕ} (h : 1 ≤ month) (lt : month < month') :
    daysBefore year month + daysIn year month ≤ daysBefore year month' := by
  obtain ⟨k, rfl⟩ : ∃ k, month' = month + 1 + k := ⟨month' - month - 1, by omega⟩
  induction k with
  | zero => rw [daysBefore_succ year h]
  | succ k ih =>
    rw [show month + 1 + (k + 1) = month + 1 + k + 1 by omega, daysBefore_succ year (by omega)]
    have := ih (by omega)
    omega

/-- A date is within its year: from the first of January to the last of
    December. -/
theorem dayNumber_in_year {year : ℤ} {month day : ℕ} (valid : DateValid year month day) :
    dayNumber year 1 1 ≤ dayNumber year month day ∧ dayNumber year month day < dayNumber (year + 1) 1 1 := by
  obtain ⟨m1, m12, d1, dIn⟩ := valid
  have mono : daysBefore year month + daysIn year month ≤ daysBefore year 13 := by
    rcases Nat.lt_or_ge month 13 with lt | ge
    · exact daysBefore_mono m1 lt
    · omega
  have total := daysBefore_thirteen year
  have leaps := leap_days year
  constructor
  · simp only [dayNumber, daysBefore_one]
    omega
  · simp only [dayNumber, daysBefore_one, add_sub_cancel_right]
    split_ifs at total leaps <;> omega

/-- Dates one after the other have growing day numbers. -/
theorem dayNumber_lt {year year' : ℤ} {month month' day day' : ℕ} (valid : DateValid year month day)
    (valid' : DateValid year' month' day')
    (lt : year < year' ∨ (year = year' ∧ (month < month' ∨ (month = month' ∧ day < day')))) :
    dayNumber year month day < dayNumber year' month' day' := by
  rcases lt with lt | ⟨rfl, lt | ⟨rfl, lt⟩⟩
  · have a := (dayNumber_in_year valid).2
    have b := (dayNumber_in_year valid').1
    have c := dayNumber_new_year_le (show year + 1 ≤ year' by omega)
    omega
  · have := daysBefore_mono (year := year) valid.1 lt
    simp only [dayNumber]
    have := valid.2.2.2
    have := valid'.2.2.1
    omega
  · simp only [dayNumber]
    omega

/-- Day numbers order the dates one after the other, and tell them apart. -/
theorem dayNumber_lt_iff {year year' : ℤ} {month month' day day' : ℕ} (valid : DateValid year month day)
    (valid' : DateValid year' month' day') :
    dayNumber year month day < dayNumber year' month' day' ↔
      year < year' ∨ (year = year' ∧ (month < month' ∨ (month = month' ∧ day < day'))) := by
  constructor
  · intro lt
    by_contra not
    rcases lt_trichotomy year year' with y | y | y
    · exact not (.inl y)
    · subst y
      rcases lt_trichotomy month month' with m | m | m
      · exact not (.inr ⟨rfl, .inl m⟩)
      · subst m
        rcases lt_trichotomy day day' with d | d | d
        · exact not (.inr ⟨rfl, .inr ⟨rfl, d⟩⟩)
        · subst d; omega
        · have := dayNumber_lt valid' valid (.inr ⟨rfl, .inr ⟨rfl, d⟩⟩); omega
      · have := dayNumber_lt valid' valid (.inr ⟨rfl, .inl m⟩); omega
    · have := dayNumber_lt valid' valid (.inl y); omega
  · exact dayNumber_lt valid valid'

theorem dayNumber_injective {year year' : ℤ} {month month' day day' : ℕ} (valid : DateValid year month day)
    (valid' : DateValid year' month' day') (same : dayNumber year month day = dayNumber year' month' day') :
    year = year' ∧ month = month' ∧ day = day' := by
  have a := (dayNumber_lt_iff valid valid').not.mp (by omega)
  have b := (dayNumber_lt_iff valid' valid).not.mp (by omega)
  push Not at a b
  rcases lt_trichotomy year year' with y | y | y
  · exact absurd y (not_lt.mpr (a.1))
  · subst y
    obtain ⟨_, ha⟩ := a
    obtain ⟨_, hb⟩ := b
    have hm := ha rfl
    have hm' := hb rfl
    have m : month = month' := le_antisymm hm'.1 hm.1
    subst m
    exact ⟨rfl, rfl, le_antisymm (hm'.2 rfl) (hm.2 rfl)⟩
  · exact absurd y (not_lt.mpr b.1)

/-! ### Places on the time line -/

/-- The time of the day of a moment in seconds, at its own offset. -/
def clockOf (m : Moment) : ℚ := ((3600 * m.hour + 60 * m.minute : ℕ) : ℚ) + m.second

theorem key_eq (m : Moment) :
    m.key = (86400 * dayNumber m.year m.month m.day : ℤ) + clockOf m - 60 * (m.zone.getD 0 : ℤ) := by
  unfold Moment.key dayNumber clockOf
  push_cast
  ring

theorem clock_bounds {m : Moment} (valid : m.Valid) : 0 ≤ clockOf m ∧ clockOf m < 86400 := by
  obtain ⟨_, _, _, _, h, mi, s0, s60, _⟩ := valid
  unfold clockOf
  constructor
  · positivity
  · have : ((3600 * m.hour + 60 * m.minute : ℕ) : ℚ) ≤ 86340 := by
      have : 3600 * m.hour + 60 * m.minute ≤ 86340 := by omega
      exact_mod_cast this
    linarith

theorem valid_date {m : Moment} (valid : m.Valid) : DateValid m.year m.month m.day :=
  ⟨valid.1, valid.2.1, valid.2.2.1, valid.2.2.2.1⟩

/-- Of two moments at one offset, the first is earlier on the time line exactly
    when its date, hour, minute and second come first one after the other. -/
theorem key_lt_iff {a b : Moment} (va : a.Valid) (vb : b.Valid) (zone : a.zone.getD 0 = b.zone.getD 0) :
    a.key < b.key ↔ dayNumber a.year a.month a.day < dayNumber b.year b.month b.day ∨
      (dayNumber a.year a.month a.day = dayNumber b.year b.month b.day ∧ clockOf a < clockOf b) := by
  rw [key_eq, key_eq, zone]
  have ca := clock_bounds va
  have cb := clock_bounds vb
  constructor
  · intro lt
    rcases lt_trichotomy (dayNumber a.year a.month a.day) (dayNumber b.year b.month b.day) with d | d | d
    · exact .inl d
    · refine .inr ⟨d, ?_⟩
      rw [d] at lt
      linarith
    · exfalso
      have : (86400 * dayNumber b.year b.month b.day : ℤ) + 86400 ≤ 86400 * dayNumber a.year a.month a.day := by
        omega
      have : ((86400 * dayNumber b.year b.month b.day : ℤ) : ℚ) + 86400 ≤
          ((86400 * dayNumber a.year a.month a.day : ℤ) : ℚ) := by exact_mod_cast this
      linarith
  · rintro (d | ⟨d, c⟩)
    · have : (86400 * dayNumber a.year a.month a.day : ℤ) + 86400 ≤ 86400 * dayNumber b.year b.month b.day := by
        omega
      have : ((86400 * dayNumber a.year a.month a.day : ℤ) : ℚ) + 86400 ≤
          ((86400 * dayNumber b.year b.month b.day : ℤ) : ℚ) := by exact_mod_cast this
      linarith
    · rw [d]; linarith

theorem clock_lt_iff {a b : Moment} (va : a.Valid) (vb : b.Valid) :
    clockOf a < clockOf b ↔ a.hour < b.hour ∨ (a.hour = b.hour ∧ (a.minute < b.minute ∨
      (a.minute = b.minute ∧ a.second < b.second))) := by
  obtain ⟨_, _, _, _, ha, ma, sa0, sa60, _⟩ := va
  obtain ⟨_, _, _, _, hb, mb, sb0, sb60, _⟩ := vb
  unfold clockOf
  constructor
  · intro lt
    by_contra not
    push Not at not
    obtain ⟨h1, h2⟩ := not
    rcases Nat.lt_or_ge b.hour a.hour with hh | hh
    · have : 3600 * b.hour + 60 * b.minute + 60 ≤ 3600 * a.hour + 60 * a.minute := by omega
      have : ((3600 * b.hour + 60 * b.minute : ℕ) : ℚ) + 60 ≤ ((3600 * a.hour + 60 * a.minute : ℕ) : ℚ) := by
        exact_mod_cast this
      linarith
    · have he : a.hour = b.hour := by omega
      obtain ⟨m1, m2⟩ := h2 he
      rcases Nat.lt_or_ge b.minute a.minute with mm | mm
      · have : 3600 * b.hour + 60 * b.minute + 60 ≤ 3600 * a.hour + 60 * a.minute := by omega
        have : ((3600 * b.hour + 60 * b.minute : ℕ) : ℚ) + 60 ≤ ((3600 * a.hour + 60 * a.minute : ℕ) : ℚ) := by
          exact_mod_cast this
        linarith
      · have me : a.minute = b.minute := by omega
        have := m2 me
        rw [he, me] at lt
        linarith
  · rintro (h | ⟨he, m | ⟨me, s⟩⟩)
    · have : 3600 * a.hour + 60 * a.minute + 60 ≤ 3600 * b.hour + 60 * b.minute := by omega
      have : ((3600 * a.hour + 60 * a.minute : ℕ) : ℚ) + 60 ≤ ((3600 * b.hour + 60 * b.minute : ℕ) : ℚ) := by
        exact_mod_cast this
      linarith
    · have : 3600 * a.hour + 60 * a.minute + 60 ≤ 3600 * b.hour + 60 * b.minute := by omega
      have : ((3600 * a.hour + 60 * a.minute : ℕ) : ℚ) + 60 ≤ ((3600 * b.hour + 60 * b.minute : ℕ) : ℚ) := by
        exact_mod_cast this
      linarith
    · rw [he, me]; linarith

/-- A place on the time line and an offset fix a moment. -/
theorem key_injective {a b : Moment} (va : a.Valid) (vb : b.Valid) (zone : a.zone = b.zone)
    (same : a.key = b.key) : a = b := by
  have z : a.zone.getD 0 = b.zone.getD 0 := by rw [zone]
  have notLt := (key_lt_iff va vb z).not.mp (by rw [same]; exact lt_irrefl _)
  have notGt := (key_lt_iff vb va z.symm).not.mp (by rw [same]; exact lt_irrefl _)
  push Not at notLt notGt
  have days : dayNumber a.year a.month a.day = dayNumber b.year b.month b.day :=
    le_antisymm notGt.1 notLt.1
  obtain ⟨y, m, d⟩ := dayNumber_injective (valid_date va) (valid_date vb) days
  have clocks : clockOf a = clockOf b := le_antisymm (notGt.2 days.symm) (notLt.2 days)
  have notLt' := (clock_lt_iff va vb).not.mp (by rw [clocks]; exact lt_irrefl _)
  have notGt' := (clock_lt_iff vb va).not.mp (by rw [clocks]; exact lt_irrefl _)
  push Not at notLt' notGt'
  have h : a.hour = b.hour := le_antisymm notGt'.1 notLt'.1
  have mi : a.minute = b.minute := le_antisymm (notGt'.2 h.symm).1 (notLt'.2 h).1
  have s : a.second = b.second := le_antisymm ((notGt'.2 h.symm).2 mi.symm) ((notLt'.2 h).2 mi)
  cases a; cases b
  simp_all

/-! ### Moving on the clock -/

/-- A moment moved by `d` minutes on the clock with the time zone `z`: the date
    moves to the day before or after when the clock passes midnight, for at
    most a day either way. -/
def shiftBy (m : Moment) (d : ℤ) (z : Option ℤ) : Moment :=
  if 60 * (m.hour : ℤ) + m.minute + d < 0 then
    ⟨(prevDate m.year m.month m.day).1, (prevDate m.year m.month m.day).2.1, (prevDate m.year m.month m.day).2.2,
      ((60 * (m.hour : ℤ) + m.minute + d + 1440) / 60).toNat, ((60 * (m.hour : ℤ) + m.minute + d + 1440) % 60).toNat,
      m.second, z⟩
  else if 60 * (m.hour : ℤ) + m.minute + d < 1440 then
    ⟨m.year, m.month, m.day, ((60 * (m.hour : ℤ) + m.minute + d) / 60).toNat,
      ((60 * (m.hour : ℤ) + m.minute + d) % 60).toNat, m.second, z⟩
  else
    ⟨(nextDate m.year m.month m.day).1, (nextDate m.year m.month m.day).2.1, (nextDate m.year m.month m.day).2.2,
      ((60 * (m.hour : ℤ) + m.minute + d - 1440) / 60).toNat, ((60 * (m.hour : ℤ) + m.minute + d - 1440) % 60).toNat,
      m.second, z⟩

/-- Two moments with one second whose days, hours and minutes less offsets
    differ by `c` minutes are `c` minutes apart on the time line. -/
theorem key_of_parts {a b : Moment} (sec : a.second = b.second) (c : ℤ)
    (h : 86400 * dayNumber a.year a.month a.day + 3600 * (a.hour : ℤ) + 60 * ((a.minute : ℤ) - a.zone.getD 0) =
      86400 * dayNumber b.year b.month b.day + 3600 * (b.hour : ℤ) + 60 * ((b.minute : ℤ) - b.zone.getD 0) +
        60 * c) :
    a.key = b.key + 60 * c := by
  rw [key_eq, key_eq]
  unfold clockOf
  rw [sec]
  have h' : ((86400 * dayNumber a.year a.month a.day + 3600 * (a.hour : ℤ) + 60 * ((a.minute : ℤ) - a.zone.getD 0) :
      ℤ) : ℚ) = ((86400 * dayNumber b.year b.month b.day + 3600 * (b.hour : ℤ) +
        60 * ((b.minute : ℤ) - b.zone.getD 0) + 60 * c : ℤ) : ℚ) := by exact_mod_cast h
  push_cast at h' ⊢
  linarith

/-- A moment moved on the clock by `d` minutes is `d` minutes later on the
    time line, less the change of its offset. -/
theorem key_shiftBy {m : Moment} (valid : m.Valid) {d : ℤ} (lo : -1440 ≤ d) (hi : d ≤ 1440) (z : Option ℤ) :
    (shiftBy m d z).key = m.key + 60 * (d + (m.zone.getD 0 - z.getD 0)) := by
  obtain ⟨m1, m12, d1, dIn, h24, mi60, _, _, _, _⟩ := valid
  have date : DateValid m.year m.month m.day := ⟨m1, m12, d1, dIn⟩
  rw [show (60 : ℚ) * ((d : ℚ) + ((m.zone.getD 0 : ℤ) - (z.getD 0 : ℤ))) =
    60 * ((d + (m.zone.getD 0 - z.getD 0) : ℤ) : ℚ) by push_cast; ring]
  unfold shiftBy
  split_ifs with neg big
  · refine key_of_parts (b := m) ?_ _ ?_
    · rfl
    have prev := dayNumber_prev date
    have e1 : (((60 * (m.hour : ℤ) + m.minute + d + 1440) / 60).toNat : ℤ) =
        (60 * (m.hour : ℤ) + m.minute + d + 1440) / 60 := Int.toNat_of_nonneg (by omega)
    have e2 : (((60 * (m.hour : ℤ) + m.minute + d + 1440) % 60).toNat : ℤ) =
        (60 * (m.hour : ℤ) + m.minute + d + 1440) % 60 := Int.toNat_of_nonneg (by omega)
    dsimp only
    rw [prev, e1, e2]
    omega
  · refine key_of_parts (b := m) ?_ _ ?_
    · rfl
    have e1 : (((60 * (m.hour : ℤ) + m.minute + d) / 60).toNat : ℤ) = (60 * (m.hour : ℤ) + m.minute + d) / 60 :=
      Int.toNat_of_nonneg (by omega)
    have e2 : (((60 * (m.hour : ℤ) + m.minute + d) % 60).toNat : ℤ) = (60 * (m.hour : ℤ) + m.minute + d) % 60 :=
      Int.toNat_of_nonneg (by omega)
    dsimp only
    rw [e1, e2]
    omega
  · refine key_of_parts (b := m) ?_ _ ?_
    · rfl
    have next := dayNumber_next date
    have e1 : (((60 * (m.hour : ℤ) + m.minute + d - 1440) / 60).toNat : ℤ) =
        (60 * (m.hour : ℤ) + m.minute + d - 1440) / 60 := Int.toNat_of_nonneg (by omega)
    have e2 : (((60 * (m.hour : ℤ) + m.minute + d - 1440) % 60).toNat : ℤ) =
        (60 * (m.hour : ℤ) + m.minute + d - 1440) % 60 := Int.toNat_of_nonneg (by omega)
    dsimp only
    rw [next, e1, e2]
    omega

/-- A moment moved on the clock is a moment, with an offset of at most
    fourteen hours. -/
theorem shiftBy_valid {m : Moment} (valid : m.Valid) {d : ℤ} (lo : -1440 ≤ d) (hi : d ≤ 1440) {z : Option ℤ}
    (zone : ∀ w, z = some w → -840 ≤ w ∧ w ≤ 840) : (shiftBy m d z).Valid := by
  obtain ⟨m1, m12, d1, dIn, h24, mi60, s0, s60, dec, _⟩ := valid
  have date : DateValid m.year m.month m.day := ⟨m1, m12, d1, dIn⟩
  unfold shiftBy
  split_ifs with neg big
  · obtain ⟨a, b, c, e⟩ := prevDate_valid date
    exact ⟨a, b, c, e, by dsimp only; omega, by dsimp only; omega, s0, s60, dec, zone⟩
  · exact ⟨m1, m12, d1, dIn, by dsimp only; omega, by dsimp only; omega, s0, s60, dec, zone⟩
  · obtain ⟨a, b, c, e⟩ := nextDate_date_valid date
    exact ⟨a, b, c, e, by dsimp only; omega, by dsimp only; omega, s0, s60, dec, zone⟩

/-! ### The values at an instant -/

/-- The moments with a time zone at the place of a moment on the time line. -/
def zonedAt (b : Moment) : Set Moment := {x | x.Valid ∧ x.zone.isSome = true ∧ x.key = b.key}

/-- There are 1681 of them: one for each offset from -14:00 to +14:00 in
    minutes. -/
theorem zonedAt_card {b : Moment} (valid : b.Valid) (none : b.zone = none) : (zonedAt b).ncard = 1681 := by
  have image : zonedAt b = (fun w : ℤ => shiftBy b w (some w)) '' Set.Icc (-840) 840 := by
    ext x
    constructor
    · rintro ⟨vx, zx, kx⟩
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp zx
      have range := vx.2.2.2.2.2.2.2.2.2 w hw
      refine ⟨w, ⟨range.1, range.2⟩, ?_⟩
      apply key_injective (shiftBy_valid valid (by omega) (by omega) (fun w' e => by cases e; exact range)) vx
      · simp [shiftBy, hw]; split_ifs <;> rfl
      · rw [key_shiftBy valid (by omega) (by omega), kx, none]
        simp
    · rintro ⟨w, ⟨lo, hi⟩, rfl⟩
      refine ⟨shiftBy_valid valid (by omega) (by omega) (fun w' e => by cases e; exact ⟨lo, hi⟩), ?_, ?_⟩
      · simp [shiftBy]; split_ifs <;> rfl
      · rw [key_shiftBy valid (by omega) (by omega), none]
        simp
  rw [image, Set.InjOn.ncard_image]
  · rw [← Finset.coe_Icc, Set.ncard_coe_finset, Int.card_Icc]
    rfl
  · intro w _ w' _ same
    have := congrArg Moment.zone same
    simp only [shiftBy] at this
    split_ifs at this <;> simpa using this

/-- The moments without a time zone at the place of a moment without one: the
    moment itself. -/
theorem unzoned_at {b x : Moment} (vb : b.Valid) (vx : x.Valid) (zb : b.zone = none) (zx : x.zone = none)
    (same : x.key = b.key) : x = b :=
  key_injective vx vb (by rw [zb, zx]) same

/-! ### The kernel's days and clock -/

private theorem new_val' : (alloc.vec.Vec.new U8).val = [] := rfl

theorem previous_year_spec (negative : Bool) (year : alloc.vec.Vec U8) (cy : Rowl.Numbers.Canonical year.val)
    (sign : negative = true → year.val ≠ []) (small : year.val.length + 2 < Usize.max) :
    ∃ n y', moments.previous_year negative year = .ok (n, y') ∧ Rowl.Numbers.Canonical y'.val ∧
      (n = true → y'.val ≠ []) ∧
      (if n then -1 else 1) * (digitsValue y'.val : ℤ) = (if negative then -1 else 1) * (digitsValue year.val : ℤ) - 1 ∧
      y'.val.length ≤ year.val.length + 2 := by
  rw [moments.previous_year]
  obtain ⟨one, oneRun, oneValue⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec (alloc.vec.Vec.new U8) 49#u8 (by simp [new_val']; scalar_tac))
  have oneIs : one.val = [49#u8] := by rw [oneValue]; simp [new_val']
  have oneDigits : digitsValue one.val = 1 := by simp [oneIs, Rowl.Numbers.value_cons, Rowl.Numbers.value_nil]
  have oneCanonical : Rowl.Numbers.Canonical one.val := by rw [oneIs]; exact Rowl.Moments.one_canonical
  simp only [oneRun, bind_ok]
  cases negative with
  | true =>
    obtain ⟨sum, run, cs, value, len⟩ := Rowl.Numbers.add_naturals_spec year one cy.1 oneCanonical.1
      (by rw [oneIs]; simp; omega)
    refine ⟨true, sum, by simp [run], cs, ?_, ?_, ?_⟩
    · intro _ e
      rw [e, Rowl.Numbers.value_nil] at value
      omega
    · simp only [oneDigits] at value
      simp [value]
      ring
    · rw [oneIs] at len; simp at len; omega
  | false =>
    by_cases empty : year.val = []
    · have lenZero : alloc.vec.Vec.len year = 0#usize := by
        apply UScalar.eq_of_val_eq; simp [empty]
      refine ⟨true, one, by simp [lenZero], oneCanonical, by simp [oneIs], ?_, by rw [oneIs]; simp⟩
      simp [oneDigits, empty, Rowl.Numbers.value_nil]
    · have lenNot : alloc.vec.Vec.len year ≠ 0#usize := by
        intro h; apply empty; have := congrArg UScalar.val h; simpa using this
      have positive : 1 ≤ digitsValue year.val := by
        have := (Rowl.Numbers.canonical_zero year.val cy).not.mpr empty; omega
      obtain ⟨rest, run, cr, value, len⟩ := Rowl.Numbers.subtract_naturals_spec year one cy oneCanonical
        (by rw [oneDigits]; exact positive) (by omega)
      refine ⟨false, rest, by simp [lenNot, run], cr, by simp, ?_, by omega⟩
      simp only [oneDigits] at value
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
      push_cast [value]
      omega

/-- The year of a kernel moment, without its sign. -/
theorem year_natAbs (x : datatypes.Moment) : (momentOf x).year.natAbs = digitsValue x.year.val := by
  simp only [momentOf]; split <;> simp

theorem following_day_spec (x : datatypes.Moment) (ok : DateOk x) :
    ∃ x', moments.following_day x = .ok x' ∧ Rowl.Numbers.Canonical x'.year.val ∧
      (x'.negative = true → x'.year.val ≠ []) ∧
      ((momentOf x').year, (momentOf x').month, (momentOf x').day) =
        nextDate (momentOf x).year x.month.val x.day.val ∧
      x'.hour = x.hour ∧ x'.minute = x.minute ∧ x'.second = x.second ∧ x'.fraction = x.fraction ∧ x'.zone = x.zone ∧
      x'.year.val.length ≤ x.year.val.length + 2 := by
  obtain ⟨cy, sign, small, m1, m12, d1, dIn⟩ := ok
  rw [moments.following_day]
  obtain ⟨days, daysRun, daysValue⟩ := Rowl.Moments.month_days_correct x.year cy.1 (momentOf x).year
    (year_natAbs x) x.month
  have daysBound := daysIn_bounds (momentOf x).year x.month.val
  by_cases before : x.day.val < daysIn (momentOf x).year x.month.val
  · have lt : x.day < days := by simp only [UScalar.lt_equiv]; omega
    obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (U8.add_spec (x := x.day) (y := 1#u8) (by scalar_tac))
    refine ⟨{ x with day := next }, by simp only [daysRun, bind_ok, lt, ↓reduceIte, add], cy, sign, ?_,
      rfl, rfl, rfl, rfl, rfl, by simp⟩
    rw [nextDate, if_pos before]
    simp at nextValue
    simp [momentOf, nextValue]
  · have notLt : ¬ x.day < days := by simp only [UScalar.lt_equiv]; omega
    by_cases early : x.month.val < 12
    · have lt : x.month < 12#u8 := by simp only [UScalar.lt_equiv]; simpa using early
      obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (U8.add_spec (x := x.month) (y := 1#u8) (by scalar_tac))
      refine ⟨{ x with month := next, day := 1#u8 },
        by simp only [daysRun, bind_ok, notLt, lt, ↓reduceIte, add], cy, sign, ?_, rfl, rfl, rfl, rfl, rfl,
        by simp⟩
      rw [nextDate, if_neg before, if_pos early]
      simp at nextValue
      simp [momentOf, nextValue]
    · have notLt' : ¬ x.month < 12#u8 := by simp only [UScalar.lt_equiv]; simpa using early
      obtain ⟨n, y', run, cy', sign', value, len⟩ := Rowl.Moments.next_year_spec x.negative x.year cy sign small
      refine ⟨{ x with negative := n, year := y', month := 1#u8, day := 1#u8 },
        by simp only [daysRun, bind_ok, notLt, notLt', ↓reduceIte, run]; rfl, cy', sign', ?_, rfl, rfl, rfl,
        rfl, rfl, len⟩
      have this : (momentOf { x with negative := n, year := y', month := 1#u8, day := 1#u8 }).year =
          (momentOf x).year + 1 := by simp only [momentOf]; exact value
      rw [nextDate, if_neg before, if_neg early, this]
      simp [momentOf]

theorem previous_day_spec (x : datatypes.Moment) (ok : DateOk x) :
    ∃ x', moments.previous_day x = .ok x' ∧ Rowl.Numbers.Canonical x'.year.val ∧
      (x'.negative = true → x'.year.val ≠ []) ∧
      ((momentOf x').year, (momentOf x').month, (momentOf x').day) =
        prevDate (momentOf x).year x.month.val x.day.val ∧
      x'.hour = x.hour ∧ x'.minute = x.minute ∧ x'.second = x.second ∧ x'.fraction = x.fraction ∧ x'.zone = x.zone ∧
      x'.year.val.length ≤ x.year.val.length + 2 := by
  obtain ⟨cy, sign, small, m1, m12, d1, dIn⟩ := ok
  rw [moments.previous_day]
  by_cases later : 1 < x.day.val
  · have lt : 1#u8 < x.day := by simp only [UScalar.lt_equiv]; simpa using later
    obtain ⟨prev, sub, prevValue⟩ := WP.spec_imp_exists (U8.sub_spec (x := x.day) (y := 1#u8) (by scalar_tac))
    refine ⟨{ x with day := prev }, by simp only [lt, ↓reduceIte, sub, bind_ok], cy, sign, ?_, rfl, rfl, rfl, rfl, rfl,
      by simp⟩
    rw [prevDate, if_pos later]
    simp at prevValue
    simp [momentOf, prevValue.1]
  · have notLt : ¬ 1#u8 < x.day := by simp only [UScalar.lt_equiv]; simpa using later
    by_cases laterMonth : 1 < x.month.val
    · have lt : 1#u8 < x.month := by simp only [UScalar.lt_equiv]; simpa using laterMonth
      obtain ⟨prev, sub, prevValue⟩ := WP.spec_imp_exists (U8.sub_spec (x := x.month) (y := 1#u8) (by scalar_tac))
      obtain ⟨days, daysRun, daysValue⟩ := Rowl.Moments.month_days_correct x.year cy.1 (momentOf x).year
        (year_natAbs x) prev
      refine ⟨{ x with month := prev, day := days }, by simp only [notLt, lt, ↓reduceIte, sub, bind_ok, daysRun],
        cy, sign, ?_, rfl, rfl, rfl, rfl, rfl, by simp⟩
      rw [prevDate, if_neg later, if_pos laterMonth]
      simp at prevValue
      simp [momentOf, prevValue.1, daysValue]
    · have notLt' : ¬ 1#u8 < x.month := by simp only [UScalar.lt_equiv]; simpa using laterMonth
      obtain ⟨n, y', run, cy', sign', value, len⟩ := previous_year_spec x.negative x.year cy sign small
      refine ⟨{ x with negative := n, year := y', month := 12#u8, day := 31#u8 },
        by simp only [notLt, notLt', ↓reduceIte, run, bind_ok]; rfl, cy', sign', ?_, rfl, rfl, rfl, rfl, rfl, len⟩
      have this : (momentOf { x with negative := n, year := y', month := 12#u8, day := 31#u8 }).year =
          (momentOf x).year - 1 := by simp only [momentOf]; exact value
      rw [prevDate, if_neg later, if_neg laterMonth, this]
      simp [momentOf]

theorem at_clock_spec (x : datatypes.Moment) (clock : U16) (h : clock.val < 1440) :
    ∃ hour minute : U8, moments.at_clock x clock = .ok { x with hour, minute, zone := none } ∧
      hour.val = clock.val / 60 ∧ minute.val = clock.val % 60 := by
  rw [moments.at_clock]
  obtain ⟨q, div, qValue⟩ := UScalar.div_spec clock (y := 60#u16) (by simp)
  obtain ⟨r, rem, rValue⟩ := WP.spec_imp_exists (UScalar.rem_spec clock (y := 60#u16) (by simp))
  have qSmall : q.val < 256 := by rw [qValue]; simp; omega
  have rSmall : r.val < 256 := by rw [rValue]; simp; omega
  refine ⟨UScalar.cast .U8 q, UScalar.cast .U8 r, by simp [div, rem, lift], ?_, ?_⟩
  · rw [UScalar.cast_val_eq, Nat.mod_eq_of_lt (by simpa using qSmall), qValue]; simp
  · rw [UScalar.cast_val_eq, Nat.mod_eq_of_lt (by simpa using rSmall), rValue]; simp

/-- The facts of a kernel moment that moving it on the clock needs: a date of
    its year, and a time on the clock. -/
def ClockOk (x : datatypes.Moment) : Prop := DateOk x ∧ x.hour.val < 24 ∧ x.minute.val < 60

theorem nat_div_toNat (a : ℕ) : (((a : ℤ)) / 60).toNat = a / 60 := by omega

theorem nat_mod_toNat (a : ℕ) : (((a : ℤ)) % 60).toNat = a % 60 := by omega

theorem shifted_spec (x : datatypes.Moment) (later : Bool) (minutes : U16) (le : minutes.val ≤ 840)
    (ok : ClockOk x) :
    ∃ x', moments.shifted x later minutes = .ok x' ∧ Rowl.Numbers.Canonical x'.year.val ∧
      (x'.negative = true → x'.year.val ≠ []) ∧ x'.year.val.length ≤ x.year.val.length + 2 ∧
      x'.zone = none ∧ x'.second = x.second ∧ x'.fraction = x.fraction ∧
      momentOf x' = shiftBy (momentOf x) (if later then (minutes.val : ℤ) else -(minutes.val : ℤ)) none := by
  obtain ⟨date, h24, m60⟩ := ok
  obtain ⟨cy, sign, small, m1, m12, d1, dIn⟩ := date
  rw [moments.shifted]
  have hourCast : (UScalar.cast .U16 x.hour).val = x.hour.val := by
    rw [UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt (by simp; omega)
  have minuteCast : (UScalar.cast .U16 x.minute).val = x.minute.val := by
    rw [UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt (by simp; omega)
  obtain ⟨i1, mul, i1Value⟩ := WP.spec_imp_exists
    (UScalar.mul_spec (x := UScalar.cast .U16 x.hour) (y := 60#u16) (by rw [hourCast]; simp [U16.max_eq]; omega))
  obtain ⟨clock, add, clockValue⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := i1) (y := UScalar.cast .U16 x.minute) (by rw [i1Value, hourCast, minuteCast]; simp [U16.max_eq]; omega))
  have clockIs : clock.val = 60 * x.hour.val + x.minute.val := by
    rw [clockValue, i1Value, hourCast, minuteCast]; simp; ring
  simp only [lift, bind_ok, mul, add]
  have dateOk : ∀ hour minute : U8, DateOk { x with hour, minute, zone := none } :=
    fun _ _ => ⟨cy, sign, small, m1, m12, d1, dIn⟩
  cases later with
  | true =>
    simp only [↓reduceIte]
    obtain ⟨i3, add3, i3Value⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := clock) (y := minutes) (by rw [clockIs]; simp [U16.max_eq]; omega))
    have i3Is : i3.val = 60 * x.hour.val + x.minute.val + minutes.val := by rw [i3Value, clockIs]
    simp only [add3, bind_ok]
    by_cases same : i3.val < 1440
    · have lt : i3 < 1440#u16 := by simp only [UScalar.lt_equiv]; simpa using same
      obtain ⟨hour, minute, run, hourValue, minuteValue⟩ := at_clock_spec x i3 same
      refine ⟨{ x with hour, minute, zone := none }, by simp only [lt, ↓reduceIte, run], cy, sign, by simp, rfl,
        rfl, rfl, ?_⟩
      unfold shiftBy
      have notNeg : ¬ (60 * ((momentOf x).hour : ℤ) + (momentOf x).minute + (minutes.val : ℤ) < 0) := by
        simp only [momentOf]; omega
      have small' : 60 * ((momentOf x).hour : ℤ) + (momentOf x).minute + (minutes.val : ℤ) < 1440 := by
        simp only [momentOf]; omega
      rw [if_neg notNeg, if_pos small']
      have cast : 60 * ((momentOf x).hour : ℤ) + (momentOf x).minute + (minutes.val : ℤ) = ((i3.val : ℕ) : ℤ) := by
        simp only [momentOf]; rw [i3Is]; push_cast; ring
      rw [cast, nat_div_toNat, nat_mod_toNat]
      simp [momentOf, hourValue, minuteValue]
    · have notLt : ¬ i3 < 1440#u16 := by simp only [UScalar.lt_equiv]; simpa using same
      obtain ⟨i4, sub4, i4Value⟩ := WP.spec_imp_exists
        (UScalar.sub_spec (x := i3) (y := 1440#u16) (by simp; omega))
      have i4Is : i4.val = i3.val - 1440 := by rw [i4Value.1]; simp
      obtain ⟨hour, minute, run, hourValue, minuteValue⟩ := at_clock_spec x i4 (by rw [i4Is]; omega)
      obtain ⟨x', next, cy', sign', dateIs, hourIs, minuteIs, secondIs, fractionIs, zoneIs, len⟩ :=
        following_day_spec _ (dateOk hour minute)
      refine ⟨x', by simp only [notLt, ↓reduceIte, sub4, bind_ok, run, next], cy', sign', len, zoneIs,
        secondIs, fractionIs, ?_⟩
      unfold shiftBy
      have notNeg : ¬ (60 * ((momentOf x).hour : ℤ) + (momentOf x).minute + (minutes.val : ℤ) < 0) := by
        simp only [momentOf]; omega
      have big : ¬ (60 * ((momentOf x).hour : ℤ) + (momentOf x).minute + (minutes.val : ℤ) < 1440) := by
        simp only [momentOf]; omega
      rw [if_neg notNeg, if_neg big]
      have cast : 60 * ((momentOf x).hour : ℤ) + (momentOf x).minute + (minutes.val : ℤ) - 1440 =
          ((i4.val : ℕ) : ℤ) := by
        simp only [momentOf]; rw [i4Is]; omega
      rw [cast, nat_div_toNat, nat_mod_toNat]
      rw [show nextDate (momentOf x).year (momentOf x).month (momentOf x).day =
        ((momentOf x').year, (momentOf x').month, (momentOf x').day) from dateIs.symm]
      simp [momentOf, hourIs, minuteIs, secondIs, fractionIs, zoneIs, hourValue, minuteValue]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases fits : minutes.val ≤ clock.val
    · have le' : minutes ≤ clock := by simp only [UScalar.le_equiv]; exact fits
      obtain ⟨i3, sub3, i3Value⟩ := WP.spec_imp_exists (UScalar.sub_spec (x := clock) (y := minutes) fits)
      have i3Is : i3.val = 60 * x.hour.val + x.minute.val - minutes.val := by rw [i3Value.1, clockIs]
      obtain ⟨hour, minute, run, hourValue, minuteValue⟩ := at_clock_spec x i3 (by rw [i3Is]; omega)
      refine ⟨{ x with hour, minute, zone := none }, by simp only [le', ↓reduceIte, sub3, bind_ok, run], cy, sign,
        by simp, rfl, rfl, rfl, ?_⟩
      unfold shiftBy
      have notNeg : ¬ (60 * ((momentOf x).hour : ℤ) + (momentOf x).minute + -(minutes.val : ℤ) < 0) := by
        simp only [momentOf]; rw [clockIs] at fits; omega
      have small' : 60 * ((momentOf x).hour : ℤ) + (momentOf x).minute + -(minutes.val : ℤ) < 1440 := by
        simp only [momentOf]; omega
      rw [if_neg notNeg, if_pos small']
      have cast : 60 * ((momentOf x).hour : ℤ) + (momentOf x).minute + -(minutes.val : ℤ) = ((i3.val : ℕ) : ℤ) := by
        simp only [momentOf]; rw [i3Is]; rw [clockIs] at fits; omega
      rw [cast, nat_div_toNat, nat_mod_toNat]
      simp [momentOf, hourValue, minuteValue]
    · have notLe : ¬ minutes ≤ clock := by simp only [UScalar.le_equiv]; exact fits
      have over : 60 * x.hour.val + x.minute.val < minutes.val := by rw [clockIs] at fits; omega
      obtain ⟨i3, add3, i3Value⟩ := WP.spec_imp_exists
        (UScalar.add_spec (x := clock) (y := 1440#u16) (by rw [clockIs]; simp [U16.max_eq]; omega))
      have i3Is : i3.val = 60 * x.hour.val + x.minute.val + 1440 := by rw [i3Value, clockIs]; simp
      obtain ⟨i4, sub4, i4Value⟩ := WP.spec_imp_exists
        (UScalar.sub_spec (x := i3) (y := minutes) (by rw [i3Is]; omega))
      have i4Is : i4.val = 60 * x.hour.val + x.minute.val + 1440 - minutes.val := by rw [i4Value.1, i3Is]
      obtain ⟨hour, minute, run, hourValue, minuteValue⟩ := at_clock_spec x i4 (by rw [i4Is]; omega)
      obtain ⟨x', prev, cy', sign', dateIs, hourIs, minuteIs, secondIs, fractionIs, zoneIs, len⟩ :=
        previous_day_spec _ (dateOk hour minute)
      refine ⟨x', by simp only [notLe, ↓reduceIte, add3, sub4, bind_ok, run, prev], cy', sign', len, zoneIs,
        secondIs, fractionIs, ?_⟩
      unfold shiftBy
      have neg : 60 * ((momentOf x).hour : ℤ) + (momentOf x).minute + -(minutes.val : ℤ) < 0 := by
        simp only [momentOf]; omega
      rw [if_pos neg]
      have cast : 60 * ((momentOf x).hour : ℤ) + (momentOf x).minute + -(minutes.val : ℤ) + 1440 =
          ((i4.val : ℕ) : ℤ) := by
        simp only [momentOf]; rw [i4Is]; omega
      rw [cast, nat_div_toNat, nat_mod_toNat]
      rw [show prevDate (momentOf x).year (momentOf x).month (momentOf x).day =
        ((momentOf x').year, (momentOf x').month, (momentOf x').day) from dateIs.symm]
      simp [momentOf, hourIs, minuteIs, secondIs, fractionIs, zoneIs, hourValue, minuteValue]

/-- A moment with another time zone moves on the time line by the change of
    its offset. -/
theorem key_zone (m : Moment) (z : Option ℤ) : { m with zone := z }.key = m.key + 60 * (m.zone.getD 0 - z.getD 0) := by
  cases m
  unfold Moment.key
  dsimp only
  push_cast
  ring

theorem vec_eq {α : Type} {a b : alloc.vec.Vec α} (h : a.val = b.val) : a = b := alloc.vec.Vec.ext a b h

/-- The kernel puts a moment at its instant: itself without a time zone, and at
    UTC with one; the instant is written canonically and keeps the place on the
    time line. -/
theorem instant_spec (x : datatypes.Moment) (c : CanonicalMoment x) (small : x.year.val.length + 2 < Usize.max) :
    ∃ x', moments.instant x = .ok x' ∧ CanonicalMoment x' ∧ x'.zone = none ∧
      (momentOf x').key = (momentOf x).key ∧ x'.year.val.length ≤ x.year.val.length + 2 ∧
      (x.zone = none → x' = x) := by
  obtain ⟨cy, sign, df, last, s60, zoneOk, valid⟩ := c
  rw [moments.instant]
  obtain ⟨v, vRun, vValue⟩ := Rowl.Moments.copy_all_spec x.year
  obtain ⟨v1, v1Run, v1Value⟩ := Rowl.Moments.copy_all_spec x.fraction
  have vIs : v = x.year := vec_eq vValue
  have v1Is : v1 = x.fraction := vec_eq v1Value
  simp only [vRun, v1Run, bind_ok, vIs, v1Is]
  have validNone : (momentOf { x with zone := none }).Valid := by
    obtain ⟨a, b, c', d, e, f, g, h, i, _⟩ := valid
    exact ⟨a, b, c', d, e, f, g, h, i, by simp [momentOf]⟩
  cases zx : x.zone with
  | none =>
    have same : { x with zone := none } = x := by cases x; simp_all
    refine ⟨x, by simp [same], ⟨cy, sign, df, last, s60, zoneOk, valid⟩, zx, rfl, by omega, fun _ => rfl⟩
  | some t =>
    obtain ⟨west, hours, minutes⟩ := t
    obtain ⟨m60, _⟩ := zoneOk west hours minutes zx
    have range := valid.2.2.2.2.2.2.2.2.2 ((if west then -1 else 1) * ((60 * hours.val + minutes.val : ℕ) : ℤ))
      (by simp [momentOf, zx])
    have total : 60 * hours.val + minutes.val ≤ 840 := by
      cases west <;> simp at range <;> omega
    have hoursCast : (UScalar.cast .U16 hours).val = hours.val := by
      rw [UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt (by simp; omega)
    have minutesCast : (UScalar.cast .U16 minutes).val = minutes.val := by
      rw [UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt (by simp; omega)
    obtain ⟨i3, mul, i3Value⟩ := WP.spec_imp_exists
      (UScalar.mul_spec (x := UScalar.cast .U16 hours) (y := 60#u16) (by rw [hoursCast]; simp [U16.max_eq]; omega))
    obtain ⟨i5, add, i5Value⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := i3) (y := UScalar.cast .U16 minutes)
        (by rw [i3Value, hoursCast, minutesCast]; simp [U16.max_eq]; omega))
    have i5Is : i5.val = 60 * hours.val + minutes.val := by
      rw [i5Value, i3Value, hoursCast, minutesCast]; simp; ring
    have clockOk : ClockOk { x with zone := none } :=
      ⟨⟨cy, sign, small, valid.1, valid.2.1, valid.2.2.1, valid.2.2.2.1⟩, valid.2.2.2.2.1, valid.2.2.2.2.2.1⟩
    obtain ⟨x', run, cy', sign', len, zone', second', fraction', shift⟩ :=
      shifted_spec { x with zone := none } west i5 (by rw [i5Is]; exact total) clockOk
    have shiftValid : (momentOf x').Valid := by
      rw [shift]
      exact shiftBy_valid validNone (by split <;> omega) (by split <;> omega) (fun w e => by cases e)
    refine ⟨x', by simp [lift, mul, add, run], ⟨cy', sign', ?_, ?_, ?_, ?_, shiftValid⟩, zone', ?_, len,
      fun h => by simp at h⟩
    · rw [fraction']; exact df
    · rw [fraction']; exact last
    · rw [second']; exact s60
    · intro w h m e; rw [zone'] at e; cases e
    · rw [shift, key_shiftBy validNone (by split <;> omega) (by split <;> omega)]
      have : momentOf { x with zone := none } = { momentOf x with zone := none } := rfl
      rw [this, key_zone]
      have zoneIs : (momentOf x).zone = some ((if west then -1 else 1) * ((60 * hours.val + minutes.val : ℕ) : ℤ)) := by
        simp [momentOf, zx]
      rw [zoneIs, i5Is]
      cases west <;> simp <;> ring

/-- Whether the kernel moment has a time zone. -/
theorem zoned_spec (x : datatypes.Moment) : moments.zoned x = .ok x.zone.isSome := by
  rw [moments.zoned]; cases x.zone <;> rfl

/-! ### Comparing instants -/

/-- The order of two values as the kernel writes it: 0 when the first comes
    first, 1 when they are equal, 2 when it comes after. -/
def ordOf {α : Type} [LinearOrder α] (a b : α) : ℕ := if a < b then 0 else if a = b then 1 else 2

/-- The first order, or the second when the first is equal. -/
def thenOrd (first second : ℕ) : ℕ := if first = 1 then second else first

theorem ordOf_congr {α β : Type} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β} (lt : a < b ↔ c < d)
    (eq : a = b ↔ c = d) : ordOf a b = ordOf c d := by
  unfold ordOf
  by_cases h : a < b
  · rw [if_pos h, if_pos (lt.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (lt.mpr h'))]
    by_cases e : a = b
    · rw [if_pos e, if_pos (eq.mp e)]
    · rw [if_neg e, if_neg (fun e' => e (eq.mpr e'))]

theorem thenOrd_lex {α β : Type} [LinearOrder α] [LinearOrder β] (a b : α) (c d : β) :
    thenOrd (ordOf a b) (ordOf c d) = ordOf (toLex (a, c)) (toLex (b, d)) := by
  unfold thenOrd
  simp only [ordOf, Prod.Lex.toLex_lt_toLex, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h, ne_of_lt h]
  · simp
  · simp [h, ne_of_gt h, not_lt_of_gt h]

theorem then_spec (a b : U8) : moments.then a b = .ok (if a = 1#u8 then b else a) := by
  rw [moments.then]
  split <;> rfl

theorem then_val (a b : U8) : (if a = 1#u8 then b else a).val = thenOrd a.val b.val := by
  unfold thenOrd
  by_cases h : a = 1#u8
  · rw [if_pos h, if_pos (by rw [h]; rfl)]
  · rw [if_neg h, if_neg (fun e => h (UScalar.eq_of_val_eq (by simpa using e)))]

theorem small_order_spec (a b : U8) : ∃ o, moments.small_order a b = .ok o ∧ o.val = ordOf a.val b.val := by
  rw [moments.small_order]
  unfold ordOf
  by_cases lt : a.val < b.val
  · exact ⟨0#u8, by simp [UScalar.lt_equiv, lt], by simp [lt]⟩
  · by_cases gt : b.val < a.val
    · exact ⟨2#u8, by simp [UScalar.lt_equiv, lt, gt], by simp [lt]; omega⟩
    · exact ⟨1#u8, by simp [UScalar.lt_equiv, lt, gt], by simp [lt]; omega⟩

/-- The kernel orders two signed years written canonically. -/
theorem year_order_spec (ln : Bool) (l : alloc.vec.Vec U8) (rn : Bool) (r : alloc.vec.Vec U8)
    (cl : Rowl.Numbers.Canonical l.val) (cr : Rowl.Numbers.Canonical r.val) (sl : ln = true → l.val ≠ [])
    (sr : rn = true → r.val ≠ []) :
    ∃ o, moments.year_order ln l rn r = .ok o ∧
      o.val = ordOf ((if ln then -1 else 1) * (digitsValue l.val : ℤ)) ((if rn then -1 else 1) * (digitsValue r.val : ℤ)) := by
  rw [moments.year_order]
  obtain ⟨c, cRun, cValue⟩ := Rowl.Numbers.compare_naturals_spec l r cl cr
  have positive : ∀ (v : alloc.vec.Vec U8), Rowl.Numbers.Canonical v.val → v.val ≠ [] → 1 ≤ digitsValue v.val :=
    fun v cv ne => by have := (Rowl.Numbers.canonical_zero v.val cv).not.mpr ne; omega
  have cBound : c.val ≤ 2 := by rw [cValue]; unfold Rowl.Numbers.order; split_ifs <;> omega
  cases ln <;> cases rn
  · refine ⟨c, by simp [cRun], ?_⟩
    rw [cValue]
    unfold ordOf Rowl.Numbers.order
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, Nat.cast_lt, Nat.cast_inj]
  · have := positive r cr (sr rfl)
    refine ⟨2#u8, by simp, ?_⟩
    unfold ordOf
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_mul]
    split_ifs <;> simp <;> omega
  · have := positive l cl (sl rfl)
    refine ⟨0#u8, by simp, ?_⟩
    unfold ordOf
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_mul]
    split_ifs <;> simp <;> omega
  · obtain ⟨d, dRun, dValue⟩ := WP.spec_imp_exists
      (UScalar.sub_spec (x := 2#u8) (y := c) (by simp; omega))
    refine ⟨d, by simp [cRun, dRun], ?_⟩
    rw [dValue.1, cValue]
    unfold ordOf Rowl.Numbers.order
    simp only [↓reduceIte, neg_mul, one_mul, neg_lt_neg_iff, neg_inj, Nat.cast_lt, Nat.cast_inj]
    split_ifs <;> simp <;> omega

theorem fraction_digit_spec (f : alloc.vec.Vec U8) (i : Usize) :
    ∃ d, moments.fraction_digit f i = .ok d ∧
      (i.val < f.val.length → ∃ h : i.val < f.val.length, d = f.val[i.val]'h) ∧ (f.val.length ≤ i.val → d = 48#u8) := by
  rw [moments.fraction_digit]
  by_cases inside : i.val < f.val.length
  · have lookup : f.index_usize i = .ok (f.val[i.val]'inside) := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    refine ⟨f.val[i.val]'inside, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup],
      fun _ => ⟨inside, rfl⟩, fun h => absurd inside (by omega)⟩
  · exact ⟨48#u8, by simp [UScalar.lt_equiv, inside], fun h => absurd h inside, fun _ => rfl⟩

theorem fractionValue_cons (d : U8) (ds : List U8) :
    fractionValue (d :: ds) = (((d.val - 48 : ℕ) : ℚ) + fractionValue ds) / 10 := by
  unfold fractionValue
  rw [Rowl.Numbers.value_cons]
  simp only [List.length_cons]
  push_cast
  field_simp
  ring

/-- Two fractions after a digit each: by the digits first, then by the rest. -/
theorem ordOf_digits (A B : ℕ) (X Y : ℚ) (hX : 0 ≤ X ∧ X < 1) (hY : 0 ≤ Y ∧ Y < 1) :
    ordOf (((A : ℚ) + X) / 10) (((B : ℚ) + Y) / 10) = thenOrd (ordOf A B) (ordOf X Y) := by
  rw [thenOrd_lex]
  apply ordOf_congr
  · rw [Prod.Lex.toLex_lt_toLex]
    constructor
    · intro lt
      rcases lt_trichotomy A B with h | h | h
      · exact .inl h
      · subst h; exact .inr ⟨rfl, by linarith⟩
      · exfalso
        have : (B : ℚ) + 1 ≤ A := by exact_mod_cast h
        linarith
    · rintro (h | ⟨h, lt⟩)
      · have : (A : ℚ) + 1 ≤ B := by exact_mod_cast h
        linarith
      · simp only at h lt
        subst h; linarith
  · simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
    constructor
    · intro e
      have e' : (A : ℚ) + X = B + Y := by linarith
      rcases lt_trichotomy A B with h | h | h
      · exfalso
        have : (A : ℚ) + 1 ≤ B := by exact_mod_cast h
        linarith
      · subst h; exact ⟨rfl, by linarith⟩
      · exfalso
        have : (B : ℚ) + 1 ≤ A := by exact_mod_cast h
        linarith
    · rintro ⟨rfl, rfl⟩; rfl

/-- The kernel orders two fractions of a second from the digit `index` on,
    missing digits counting as zeros. -/
theorem fraction_order_spec (l r : alloc.vec.Vec U8) (dl : Digits l.val) (dr : Digits r.val) (i : Usize) :
    ∃ o, moments.fraction_order l r i = .ok o ∧
      o.val = ordOf (fractionValue (l.val.drop i.val)) (fractionValue (r.val.drop i.val)) := by
  rw [moments.fraction_order]
  by_cases inside : i.val < l.val.length ∨ i.val < r.val.length
  · have cond : ((decide (i < alloc.vec.Vec.len l)) || (decide (i < alloc.vec.Vec.len r))) = true := by
      rcases inside with h | h
      · simp [UScalar.lt_equiv, h]
      · simp [UScalar.lt_equiv, h]
    have room : i.val + 1 ≤ Usize.max := by
      have := l.property; have := r.property; omega
    obtain ⟨a, aRun, aIn, aOut⟩ := fraction_digit_spec l i
    obtain ⟨b, bRun, bIn, bOut⟩ := fraction_digit_spec r i
    obtain ⟨o1, o1Run, o1Value⟩ := small_order_spec a b
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = i.val + 1 := by simpa using nextValue
    obtain ⟨o2, o2Run, o2Value⟩ := fraction_order_spec l r dl dr next
    refine ⟨if o1 = 1#u8 then o2 else o1,
      by simp only [cond, ↓reduceIte, aRun, bRun, o1Run, advance, o2Run, then_spec, bind_ok], ?_⟩
    rw [then_val, o1Value, o2Value, nextIs]
    -- each fraction is its digit and the rest after it
    have split : ∀ (f : alloc.vec.Vec U8) (df : Digits f.val) (d : U8),
        (i.val < f.val.length → ∃ h : i.val < f.val.length, d = f.val[i.val]'h) → (f.val.length ≤ i.val → d = 48#u8) →
        d.val - 48 ≤ 9 ∧
        fractionValue (f.val.drop i.val) = (((d.val - 48 : ℕ) : ℚ) + fractionValue (f.val.drop (i.val + 1))) / 10 ∧
        48 ≤ d.val := by
      intro f df d hin hout
      by_cases h : i.val < f.val.length
      · obtain ⟨h', rfl⟩ := hin h
        have digit := df _ (List.getElem_mem h')
        refine ⟨by have := digit.2; omega, ?_, digit.1⟩
        rw [List.drop_eq_getElem_cons h', fractionValue_cons]
      · rw [hout (by omega)]
        refine ⟨by simp, ?_, by simp⟩
        rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega), Rowl.Moments.fractionValue_nil]
        simp
    obtain ⟨a9, aSplit, a48⟩ := split l dl a aIn aOut
    obtain ⟨b9, bSplit, b48⟩ := split r dr b bIn bOut
    rw [aSplit, bSplit, ordOf_digits _ _ _ _
      (Rowl.Moments.fractionValue_bounds _ (fun x m => dl x (List.mem_of_mem_drop m)))
      (Rowl.Moments.fractionValue_bounds _ (fun x m => dr x (List.mem_of_mem_drop m)))]
    congr 1
    apply ordOf_congr <;> omega
  · have h1 : ¬ i < alloc.vec.Vec.len l := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact (not_or.mp inside).1
    have h2 : ¬ i < alloc.vec.Vec.len r := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact (not_or.mp inside).2
    refine ⟨1#u8, by simp [h1, h2], ?_⟩
    rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega), Rowl.Moments.fractionValue_nil]
    simp [ordOf]
termination_by max l.val.length r.val.length - i.val
decreasing_by omega

/-- The year, month, day, hour, minute, whole seconds and fraction of a kernel
    moment one after the other. -/
def lexOf (x : datatypes.Moment) : ℤ ×ₗ (ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℚ))))) :=
  toLex ((momentOf x).year, toLex (x.month.val, toLex (x.day.val, toLex (x.hour.val, toLex (x.minute.val,
    toLex (x.second.val, fractionValue x.fraction.val))))))

theorem second_lt_iff (s s' : ℕ) {f f' : ℚ} (hf : 0 ≤ f ∧ f < 1) (hf' : 0 ≤ f' ∧ f' < 1) :
    (s : ℚ) + f < s' + f' ↔ s < s' ∨ (s = s' ∧ f < f') := by
  constructor
  · intro lt
    rcases lt_trichotomy s s' with h | rfl | h
    · exact .inl h
    · exact .inr ⟨rfl, by linarith⟩
    · exfalso
      have : (s' : ℚ) + 1 ≤ s := by exact_mod_cast h
      linarith
  · rintro (h | ⟨rfl, h⟩)
    · have : (s : ℚ) + 1 ≤ s' := by exact_mod_cast h
      linarith
    · linarith

theorem second_eq_iff (s s' : ℕ) {f f' : ℚ} (hf : 0 ≤ f ∧ f < 1) (hf' : 0 ≤ f' ∧ f' < 1) :
    (s : ℚ) + f = s' + f' ↔ s = s' ∧ f = f' := by
  constructor
  · intro e
    rcases lt_trichotomy s s' with h | rfl | h
    · exfalso
      have : (s : ℚ) + 1 ≤ s' := by exact_mod_cast h
      linarith
    · exact ⟨rfl, by linarith⟩
    · exfalso
      have : (s' : ℚ) + 1 ≤ s := by exact_mod_cast h
      linarith
  · rintro ⟨rfl, rfl⟩; rfl

/-- On kernel instants, the place on the time line orders like the dates and
    times one after the other. -/
theorem key_lex {a b : datatypes.Moment} (ca : CanonicalMoment a) (cb : CanonicalMoment b) (za : a.zone = none)
    (zb : b.zone = none) :
    ((momentOf a).key < (momentOf b).key ↔ lexOf a < lexOf b) ∧
      ((momentOf a).key = (momentOf b).key ↔ lexOf a = lexOf b) := by
  have va := ca.2.2.2.2.2.2
  have vb := cb.2.2.2.2.2.2
  have fa := Rowl.Moments.fractionValue_bounds _ ca.2.2.1
  have fb := Rowl.Moments.fractionValue_bounds _ cb.2.2.1
  have zone : (momentOf a).zone.getD 0 = (momentOf b).zone.getD 0 := by simp [momentOf, za, zb]
  have days : dayNumber (momentOf a).year (momentOf a).month (momentOf a).day =
      dayNumber (momentOf b).year (momentOf b).month (momentOf b).day ↔
      (momentOf a).year = (momentOf b).year ∧ (momentOf a).month = (momentOf b).month ∧
        (momentOf a).day = (momentOf b).day :=
    ⟨dayNumber_injective (valid_date va) (valid_date vb), by rintro ⟨h1, h2, h3⟩; rw [h1, h2, h3]⟩
  have secA : (momentOf a).second = (a.second.val : ℚ) + fractionValue a.fraction.val := rfl
  have secB : (momentOf b).second = (b.second.val : ℚ) + fractionValue b.fraction.val := rfl
  constructor
  · rw [key_lt_iff va vb zone, dayNumber_lt_iff (valid_date va) (valid_date vb), clock_lt_iff va vb, days, secA,
      secB, second_lt_iff _ _ fa fb]
    simp only [lexOf, Prod.Lex.toLex_lt_toLex, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
    simp only [momentOf]
    tauto
  · constructor
    · intro same
      have eq := key_injective va vb (by simp [momentOf, za, zb]) same
      have s := congrArg Moment.second eq
      rw [secA, secB, second_eq_iff _ _ fa fb] at s
      simp only [lexOf, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
      exact ⟨congrArg Moment.year eq, congrArg Moment.month eq, congrArg Moment.day eq, congrArg Moment.hour eq,
        congrArg Moment.minute eq, s.1, s.2⟩
    · intro same
      simp only [lexOf, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at same
      obtain ⟨y, m, d, h, mi, sec, f⟩ := same
      have : momentOf a = momentOf b := by
        simp only [momentOf] at y ⊢
        rw [za, zb, Moment.mk.injEq]
        exact ⟨y, m, d, h, mi, by rw [sec, f], rfl⟩
      rw [this]

/-- The kernel compares two instants written canonically by their places on
    the time line. -/
theorem instant_order_spec (a b : datatypes.Moment) (ca : CanonicalMoment a) (cb : CanonicalMoment b)
    (za : a.zone = none) (zb : b.zone = none) :
    ∃ o, moments.instant_order a b = .ok o ∧ o.val = ordOf (momentOf a).key (momentOf b).key := by
  rw [moments.instant_order]
  obtain ⟨y, yRun, yValue⟩ := year_order_spec a.negative a.year b.negative b.year ca.1 cb.1 ca.2.1 cb.2.1
  obtain ⟨m, mRun, mValue⟩ := small_order_spec a.month b.month
  obtain ⟨d, dRun, dValue⟩ := small_order_spec a.day b.day
  obtain ⟨h, hRun, hValue⟩ := small_order_spec a.hour b.hour
  obtain ⟨mi, miRun, miValue⟩ := small_order_spec a.minute b.minute
  obtain ⟨s, sRun, sValue⟩ := small_order_spec a.second b.second
  obtain ⟨f, fRun, fValue⟩ := fraction_order_spec a.fraction b.fraction ca.2.2.1 cb.2.2.1 0#usize
  refine ⟨if y = 1#u8 then (if m = 1#u8 then (if d = 1#u8 then (if h = 1#u8 then
      (if mi = 1#u8 then (if s = 1#u8 then f else s) else mi) else h) else d) else m) else y,
    by simp only [yRun, mRun, dRun, hRun, miRun, sRun, fRun, then_spec, bind_ok], ?_⟩
  simp only [then_val]
  rw [yValue, mValue, dValue, hValue, miValue, sValue, fValue]
  have k := key_lex ca cb za zb
  rw [ordOf_congr k.1 k.2]
  simp only [thenOrd_lex, lexOf, List.drop_zero]
  rfl

/-! ### Canonical instants -/

/-- A kernel instant: a moment written canonically, without a time zone, whose
    year has room to grow. -/
def InstantOk (x : datatypes.Moment) (room : ℕ) : Prop :=
  CanonicalMoment x ∧ x.zone = none ∧ x.year.val.length + room < Usize.max

/-- Moving a kernel instant on the clock gives a kernel instant, the number of
    minutes later on the time line. -/
theorem shifted_canonical (x : datatypes.Moment) (later : Bool) (minutes : U16) (le : minutes.val ≤ 840)
    {room : ℕ} (ok : InstantOk x (room + 2)) :
    ∃ x', moments.shifted x later minutes = .ok x' ∧ InstantOk x' room ∧
      (momentOf x').key = (momentOf x).key + 60 * (if later then (minutes.val : ℤ) else -(minutes.val : ℤ)) := by
  obtain ⟨⟨cy, sign, df, last, s60, _, valid⟩, zone, small⟩ := ok
  have clockOk : ClockOk x := ⟨⟨cy, sign, by omega, valid.1, valid.2.1, valid.2.2.1, valid.2.2.2.1⟩,
    valid.2.2.2.2.1, valid.2.2.2.2.2.1⟩
  obtain ⟨x', run, cy', sign', len, zone', second', fraction', shift⟩ :=
    shifted_spec x later minutes le clockOk
  have bounds : -1440 ≤ (if later then (minutes.val : ℤ) else -(minutes.val : ℤ)) ∧
      (if later then (minutes.val : ℤ) else -(minutes.val : ℤ)) ≤ 1440 := by
    split <;> omega
  have shiftValid : (momentOf x').Valid := by
    rw [shift]
    exact shiftBy_valid valid bounds.1 bounds.2 (fun w e => by cases e)
  refine ⟨x', run, ⟨⟨cy', sign', (by rw [fraction']; exact df), (by rw [fraction']; exact last),
    (by rw [second']; exact s60), (fun w h m e => by rw [zone'] at e; cases e), shiftValid⟩, zone', (by omega)⟩, ?_⟩
  rw [shift, key_shiftBy valid bounds.1 bounds.2]
  have : (momentOf x).zone = none := by simp [momentOf, zone]
  rw [this]
  simp

/-- The instant of a kernel moment written canonically is a kernel instant at
    the same place on the time line. -/
theorem instant_canonical (x : datatypes.Moment) (c : CanonicalMoment x) {room : ℕ}
    (small : x.year.val.length + room + 2 < Usize.max) :
    ∃ x', moments.instant x = .ok x' ∧ InstantOk x' room ∧ (momentOf x').key = (momentOf x).key := by
  obtain ⟨x', run, c', zone', key', len, _⟩ := instant_spec x c (by omega)
  exact ⟨x', run, ⟨c', zone', by omega⟩, key'⟩

theorem ordOf_eq_one {α : Type} [LinearOrder α] (a b : α) : ordOf a b = 1 ↔ a = b := by
  unfold ordOf
  by_cases h : a < b
  · simp [h, ne_of_lt h]
  · by_cases e : a = b
    · simp [e]
    · simp [h, e]

theorem ordOf_eq_two {α : Type} [LinearOrder α] (a b : α) : ordOf a b = 2 ↔ b < a := by
  unfold ordOf
  by_cases h : a < b
  · simp [h, not_lt_of_gt h]
  · by_cases e : a = b
    · simp [e]
    · simp [h, e]; exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm e)

/-! ### The kernel's comparisons always answer -/

theorem compare_from_ok (l r : alloc.vec.Vec U8) (index : Usize) :
    ∃ o, numbers.compare_from l r index = .ok o ∧ o.val ≤ 2 := by
  rw [numbers.compare_from]
  by_cases inL : index.val < l.val.length
  · by_cases inR : index.val < r.val.length
    · have lookupL : l.index_usize index = .ok l.val[index.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inL]
      have lookupR : r.index_usize index = .ok r.val[index.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inR]
      by_cases lt : (l.val[index.val]).val < (r.val[index.val]).val
      · exact ⟨0#u8, by simp [UScalar.lt_equiv, inL, inR, alloc.vec.Vec.index_slice_index, lookupL, lookupR, lt],
          by simp⟩
      · by_cases gt : (r.val[index.val]).val < (l.val[index.val]).val
        · exact ⟨2#u8, by simp [UScalar.lt_equiv, inL, inR, alloc.vec.Vec.index_slice_index, lookupL, lookupR, lt,
            gt], by simp⟩
        · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
            (Usize.add_spec (x := index) (y := 1#usize) (by have := l.property; scalar_tac))
          obtain ⟨o, run, bound⟩ := compare_from_ok l r next
          exact ⟨o, by simp [UScalar.lt_equiv, inL, inR, alloc.vec.Vec.index_slice_index, lookupL, lookupR, lt, gt,
            advance, run], bound⟩
    · exact ⟨1#u8, by simp [UScalar.lt_equiv, inL, inR], by simp⟩
  · exact ⟨1#u8, by simp [UScalar.lt_equiv, inL], by simp⟩
termination_by l.val.length - index.val
decreasing_by simp_all; omega

theorem compare_naturals_ok (l r : alloc.vec.Vec U8) : ∃ o, numbers.compare_naturals l r = .ok o ∧ o.val ≤ 2 := by
  rw [numbers.compare_naturals]
  by_cases a : l.val.length < r.val.length
  · exact ⟨0#u8, by simp [UScalar.lt_equiv, a], by simp⟩
  · by_cases b : r.val.length < l.val.length
    · exact ⟨2#u8, by simp [UScalar.lt_equiv, a, b], by simp⟩
    · obtain ⟨o, run, bound⟩ := compare_from_ok l r 0#usize
      exact ⟨o, by simp [UScalar.lt_equiv, a, b, run], bound⟩

theorem year_order_ok (ln : Bool) (l : alloc.vec.Vec U8) (rn : Bool) (r : alloc.vec.Vec U8) :
    ∃ o, moments.year_order ln l rn r = .ok o := by
  rw [moments.year_order]
  obtain ⟨c, run, bound⟩ := compare_naturals_ok l r
  cases ln <;> cases rn
  · exact ⟨c, by simp [run]⟩
  · exact ⟨2#u8, by simp⟩
  · exact ⟨0#u8, by simp⟩
  · obtain ⟨d, dRun, _⟩ := WP.spec_imp_exists (UScalar.sub_spec (x := 2#u8) (y := c) (by simp; omega))
    exact ⟨d, by simp [run, dRun]⟩

theorem fraction_order_ok (l r : alloc.vec.Vec U8) (i : Usize) : ∃ o, moments.fraction_order l r i = .ok o := by
  rw [moments.fraction_order]
  by_cases inside : i.val < l.val.length ∨ i.val < r.val.length
  · have cond : ((decide (i < alloc.vec.Vec.len l)) || (decide (i < alloc.vec.Vec.len r))) = true := by
      rcases inside with h | h
      · simp [UScalar.lt_equiv, h]
      · simp [UScalar.lt_equiv, h]
    obtain ⟨a, aRun, _⟩ := fraction_digit_spec l i
    obtain ⟨b, bRun, _⟩ := fraction_digit_spec r i
    obtain ⟨o1, o1Run, _⟩ := small_order_spec a b
    have room : i.val + 1 ≤ Usize.max := by
      have hl := l.property; have hr := r.property
      rcases inside with h | h <;> omega
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := i) (y := 1#usize) (by simpa using room))
    obtain ⟨o2, o2Run⟩ := fraction_order_ok l r next
    exact ⟨if o1 = 1#u8 then o2 else o1,
      by simp only [cond, ↓reduceIte, aRun, bRun, o1Run, advance, o2Run, then_spec, bind_ok]⟩
  · have h1 : ¬ i < alloc.vec.Vec.len l := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact (not_or.mp inside).1
    have h2 : ¬ i < alloc.vec.Vec.len r := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact (not_or.mp inside).2
    exact ⟨1#u8, by simp [h1, h2]⟩
termination_by max l.val.length r.val.length - i.val
decreasing_by simp_all; omega

/-- The kernel compares any two moments. -/
theorem instant_order_ok (a b : datatypes.Moment) : ∃ o, moments.instant_order a b = .ok o := by
  rw [moments.instant_order]
  obtain ⟨y, yRun⟩ := year_order_ok a.negative a.year b.negative b.year
  obtain ⟨m, mRun, _⟩ := small_order_spec a.month b.month
  obtain ⟨d, dRun, _⟩ := small_order_spec a.day b.day
  obtain ⟨h, hRun, _⟩ := small_order_spec a.hour b.hour
  obtain ⟨mi, miRun, _⟩ := small_order_spec a.minute b.minute
  obtain ⟨s, sRun, _⟩ := small_order_spec a.second b.second
  obtain ⟨f, fRun⟩ := fraction_order_ok a.fraction b.fraction 0#usize
  exact ⟨if y = 1#u8 then (if m = 1#u8 then (if d = 1#u8 then (if h = 1#u8 then
      (if mi = 1#u8 then (if s = 1#u8 then f else s) else mi) else h) else d) else m) else y,
    by simp only [yRun, mRun, dRun, hRun, miRun, sRun, fRun, then_spec, bind_ok]⟩

end Rowl.TimeOrder
