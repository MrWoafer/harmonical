use std::{
    fmt::Display,
    num::NonZeroUsize,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use num2words::Num2Words;
use paste::paste;

use crate::{
    enharmonic::Enharmonic,
    pitches::Pitch,
    tuning::{SemitonesTET12, TET12},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MajorMinorIntervalQuality {
    Major,
    Minor,
    Augmented(NonZeroUsize),
    Diminished(NonZeroUsize),
}

impl MajorMinorIntervalQuality {
    fn index(&self) -> isize {
        match self {
            Self::Augmented(times) => 1 + times.get() as isize,
            Self::Major => 1,
            Self::Minor => 0,
            Self::Diminished(times) => -(times.get() as isize),
        }
    }

    pub(crate) fn from_index(index: isize) -> Self {
        match index {
            2.. => Self::Augmented(
                NonZeroUsize::new((index - 1) as usize).expect("should be non-zero"),
            ),
            1 => Self::Major,
            0 => Self::Minor,
            ..0 => {
                Self::Diminished(NonZeroUsize::new((-index) as usize).expect("should be non-zero"))
            }
        }
    }

    pub const fn invert(self) -> Self {
        match self {
            Self::Augmented(times) => Self::Diminished(times),
            Self::Major => Self::Minor,
            Self::Minor => Self::Major,
            Self::Diminished(times) => Self::Augmented(times),
        }
    }

    pub const fn augment(self) -> Self {
        match self {
            Self::Augmented(times) => Self::Augmented(times.checked_add(1).expect(
                "realistically something shouldn't be augmented enough times for an overflow to \
                occur",
            )),
            Self::Major => Self::Augmented(NonZeroUsize::new(1).unwrap()),
            Self::Minor => Self::Major,
            Self::Diminished(times) => match times.get() {
                0 => unreachable!(),
                1 => Self::Minor,
                times => {
                    Self::Diminished(NonZeroUsize::new(times - 1).expect("should be non-zero"))
                }
            },
        }
    }

    pub const fn diminish(self) -> Self {
        match self {
            Self::Augmented(times) => match times.get() {
                0 => unreachable!(),
                1 => Self::Major,
                times => Self::Augmented(NonZeroUsize::new(times - 1).expect("should be non-zero")),
            },
            Self::Major => Self::Minor,
            Self::Minor => Self::Diminished(NonZeroUsize::new(1).unwrap()),
            Self::Diminished(times) => Self::Diminished(times.checked_add(1).expect(
                "realistically something shouldn't be diminished enough times for an overflow to \
                occur",
            )),
        }
    }
}

impl PartialOrd for MajorMinorIntervalQuality {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for MajorMinorIntervalQuality {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.index().cmp(&other.index())
    }
}

impl Display for MajorMinorIntervalQuality {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        IntervalQuality::from(*self).fmt(f)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PerfectIntervalQuality {
    Perfect,
    Augmented(NonZeroUsize),
    Diminished(NonZeroUsize),
}

impl PerfectIntervalQuality {
    fn index(&self) -> isize {
        match self {
            Self::Augmented(times) => times.get() as isize,
            Self::Perfect => 0,
            Self::Diminished(times) => -(times.get() as isize),
        }
    }

    pub(crate) fn from_index(index: isize) -> Self {
        match index {
            1.. => Self::Augmented(NonZeroUsize::new(index as usize).expect("should be non-zero")),
            0 => Self::Perfect,
            ..0 => {
                Self::Diminished(NonZeroUsize::new((-index) as usize).expect("should be non-zero"))
            }
        }
    }

    pub const fn invert(self) -> Self {
        match self {
            Self::Augmented(times) => Self::Diminished(times),
            Self::Perfect => Self::Perfect,
            Self::Diminished(times) => Self::Augmented(times),
        }
    }

    pub const fn augment(self) -> Self {
        match self {
            Self::Augmented(times) => Self::Augmented(times.checked_add(1).expect(
                "realistically something shouldn't be augmented enough times for an overflow to \
                occur",
            )),
            Self::Perfect => Self::Augmented(NonZeroUsize::new(1).unwrap()),
            Self::Diminished(times) => match times.get() {
                0 => unreachable!(),
                1 => Self::Perfect,
                times => {
                    Self::Diminished(NonZeroUsize::new(times - 1).expect("should be non-zero"))
                }
            },
        }
    }

    pub const fn diminish(self) -> Self {
        match self {
            Self::Augmented(times) => match times.get() {
                0 => unreachable!(),
                1 => Self::Perfect,
                times => Self::Augmented(NonZeroUsize::new(times - 1).expect("should be non-zero")),
            },
            Self::Perfect => Self::Diminished(NonZeroUsize::new(1).unwrap()),
            Self::Diminished(times) => Self::Diminished(times.checked_add(1).expect(
                "realistically something shouldn't be diminished enough times for an overflow to \
                occur",
            )),
        }
    }
}

impl PartialOrd for PerfectIntervalQuality {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PerfectIntervalQuality {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.index().cmp(&other.index())
    }
}

impl Display for PerfectIntervalQuality {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        IntervalQuality::from(*self).fmt(f)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntervalQuality {
    Perfect,
    Major,
    Minor,
    Augmented(NonZeroUsize),
    Diminished(NonZeroUsize),
}

impl IntervalQuality {
    pub const fn invert(self) -> Self {
        match self {
            Self::Augmented(times) => Self::Diminished(times),
            Self::Major => Self::Minor,
            Self::Perfect => Self::Perfect,
            Self::Minor => Self::Major,
            Self::Diminished(times) => Self::Augmented(times),
        }
    }

    pub const fn augment(self) -> Self {
        match self {
            Self::Augmented(times) => Self::Augmented(times.checked_add(1).expect(
                "realistically something shouldn't be augmented enough times for an overflow to \
                occur",
            )),
            Self::Perfect | Self::Major => Self::Augmented(NonZeroUsize::new(1).unwrap()),
            Self::Minor => Self::Major,
            Self::Diminished(times) => match times.get() {
                0 => unreachable!(),
                1 => Self::Perfect,
                times => {
                    Self::Diminished(NonZeroUsize::new(times - 1).expect("should be non-zero"))
                }
            },
        }
    }

    pub const fn diminish(self) -> Self {
        match self {
            Self::Augmented(times) => match times.get() {
                0 => unreachable!(),
                1 => Self::Perfect,
                times => Self::Augmented(NonZeroUsize::new(times - 1).expect("should be non-zero")),
            },
            Self::Major => Self::Minor,
            Self::Perfect | Self::Minor => Self::Diminished(NonZeroUsize::new(1).unwrap()),
            Self::Diminished(times) => Self::Diminished(times.checked_add(1).expect(
                "realistically something shouldn't be diminished enough times for an overflow to \
                occur",
            )),
        }
    }
}

impl From<MajorMinorIntervalQuality> for IntervalQuality {
    fn from(quality: MajorMinorIntervalQuality) -> Self {
        match quality {
            MajorMinorIntervalQuality::Major => Self::Major,
            MajorMinorIntervalQuality::Minor => Self::Minor,
            MajorMinorIntervalQuality::Augmented(times) => Self::Augmented(times),
            MajorMinorIntervalQuality::Diminished(times) => Self::Diminished(times),
        }
    }
}

impl From<PerfectIntervalQuality> for IntervalQuality {
    fn from(quality: PerfectIntervalQuality) -> Self {
        match quality {
            PerfectIntervalQuality::Perfect => Self::Perfect,
            PerfectIntervalQuality::Augmented(times) => Self::Augmented(times),
            PerfectIntervalQuality::Diminished(times) => Self::Diminished(times),
        }
    }
}

impl TryFrom<IntervalQuality> for MajorMinorIntervalQuality {
    type Error = ();

    fn try_from(quality: IntervalQuality) -> Result<Self, Self::Error> {
        match quality {
            IntervalQuality::Perfect => Err(()),
            IntervalQuality::Major => Ok(Self::Major),
            IntervalQuality::Minor => Ok(Self::Minor),
            IntervalQuality::Augmented(times) => Ok(Self::Augmented(times)),
            IntervalQuality::Diminished(times) => Ok(Self::Diminished(times)),
        }
    }
}

impl TryFrom<IntervalQuality> for PerfectIntervalQuality {
    type Error = ();

    fn try_from(quality: IntervalQuality) -> Result<Self, Self::Error> {
        match quality {
            IntervalQuality::Perfect => Ok(Self::Perfect),
            IntervalQuality::Major => Err(()),
            IntervalQuality::Minor => Err(()),
            IntervalQuality::Augmented(times) => Ok(Self::Augmented(times)),
            IntervalQuality::Diminished(times) => Ok(Self::Diminished(times)),
        }
    }
}

impl Display for IntervalQuality {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            match self {
                Self::Perfect => write!(f, "perfect"),
                Self::Major => write!(f, "major"),
                Self::Minor => write!(f, "minor"),
                Self::Augmented(times) => match times.get() {
                    0 => unreachable!(),
                    1 => write!(f, "augmented"),
                    2 => write!(f, "doubly augmented"),
                    times @ 3.. => write!(f, "{times}x augmented"),
                },
                Self::Diminished(times) => match times.get() {
                    0 => unreachable!(),
                    1 => write!(f, "diminished"),
                    2 => write!(f, "doubly diminished"),
                    times @ 3.. => write!(f, "{times}x diminished"),
                },
            }
        } else {
            match self {
                Self::Perfect => write!(f, "P"),
                Self::Major => write!(f, "M"),
                Self::Minor => write!(f, "m"),
                Self::Augmented(times) => write!(f, "{}", "A".repeat(times.get())),
                Self::Diminished(times) => write!(f, "{}", "d".repeat(times.get())),
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UnorderedSimpleIntervalNumber {
    Unison,
    Second,
    Third,
    Fourth,
    Fifth,
    Sixth,
    Seventh,
}

impl UnorderedSimpleIntervalNumber {
    pub fn zero_based(&self) -> usize {
        match self {
            Self::Unison => 0,
            Self::Second => 1,
            Self::Third => 2,
            Self::Fourth => 3,
            Self::Fifth => 4,
            Self::Sixth => 5,
            Self::Seventh => 6,
        }
    }

    pub fn one_based(&self) -> usize {
        self.zero_based() + 1
    }

    pub fn try_from_zero_based(number: usize) -> Result<Self, ()> {
        match number {
            0 => Ok(Self::Unison),
            1 => Ok(Self::Second),
            2 => Ok(Self::Third),
            3 => Ok(Self::Fourth),
            4 => Ok(Self::Fifth),
            5 => Ok(Self::Sixth),
            6 => Ok(Self::Seventh),
            _ => Err(()),
        }
    }

    pub fn try_from_one_based(number: usize) -> Result<Self, ()> {
        match number {
            0 => Err(()),
            _ => Self::try_from_zero_based(number - 1),
        }
    }

    pub fn checked_add(self, rhs: Self) -> Result<Self, ()> {
        Self::try_from_zero_based(self.zero_based() + rhs.zero_based())
    }

    pub fn wrapping_add(self, rhs: Self) -> Self {
        Self::try_from_zero_based((self.zero_based() + rhs.zero_based()).rem_euclid(7))
            .expect("should be in valid range")
    }

    pub fn checked_sub(self, rhs: Self) -> Result<Self, ()> {
        self.zero_based()
            .checked_sub(rhs.zero_based())
            .ok_or(())
            .map(|zero_based| {
                Self::try_from_zero_based(zero_based).expect("should be in valid range")
            })
    }

    pub fn wrapping_sub(self, rhs: Self) -> Self {
        Self::try_from_zero_based(if self.zero_based() >= rhs.zero_based() {
            self.zero_based() - rhs.zero_based()
        } else {
            self.zero_based() + 7 - rhs.zero_based()
        })
        .expect("should be in valid range")
    }

    pub fn checked_mul(self, rhs: usize) -> Result<Self, ()> {
        let (wrapping_mul, extra_octaves) = self.wrapping_mul_with_octaves(rhs);

        if extra_octaves == 0 {
            Ok(wrapping_mul)
        } else {
            Err(())
        }
    }

    pub fn wrapping_mul(self, rhs: usize) -> Self {
        let (wrapping_mul, _) = self.wrapping_mul_with_octaves(rhs);

        wrapping_mul
    }

    fn wrapping_mul_with_octaves(self, rhs: usize) -> (Self, usize) {
        let wrapping_mul = Self::try_from_zero_based((self.zero_based() * rhs).rem_euclid(7))
            .expect("should be in valid range");

        let extra_octaves = (self.zero_based() * rhs) / 7;

        (wrapping_mul, extra_octaves)
    }

    pub fn invert(self) -> Self {
        match self {
            Self::Unison => Self::Unison,
            Self::Second => Self::Seventh,
            Self::Third => Self::Sixth,
            Self::Fourth => Self::Fifth,
            Self::Fifth => Self::Fourth,
            Self::Sixth => Self::Third,
            Self::Seventh => Self::Second,
        }
    }
}

impl Display for UnorderedSimpleIntervalNumber {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            match self {
                Self::Unison => write!(f, "unison"),
                _ => write!(
                    f,
                    "{}",
                    Num2Words::new(self.one_based() as u32)
                        .ordinal()
                        .to_words()
                        .expect("ordinal formatting should succeed")
                ),
            }
        } else {
            write!(f, "{}", self.one_based())
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UnorderedSimpleInterval {
    Unison(PerfectIntervalQuality),
    Second(MajorMinorIntervalQuality),
    Third(MajorMinorIntervalQuality),
    Fourth(PerfectIntervalQuality),
    Fifth(PerfectIntervalQuality),
    Sixth(MajorMinorIntervalQuality),
    Seventh(MajorMinorIntervalQuality),
}

macro_rules! make_unordered_simple_interval_consts {
    (Perfect, $variant:ident, $number:literal) => {
        paste! {
            pub const [< AA$number >]: Self =
                Self::$variant(PerfectIntervalQuality::Augmented(NonZeroUsize::new(2).unwrap()));
            pub const [< A$number >]: Self =
                Self::$variant(PerfectIntervalQuality::Augmented(NonZeroUsize::new(1).unwrap()));
            pub const [< P$number >]: Self =
                Self::$variant(PerfectIntervalQuality::Perfect);
            #[expect(non_upper_case_globals)]
            pub const [< d$number >]: Self =
                Self::$variant(PerfectIntervalQuality::Diminished(NonZeroUsize::new(1).unwrap()));
            #[expect(non_upper_case_globals)]
            pub const [< dd$number >]: Self =
                Self::$variant(PerfectIntervalQuality::Diminished(NonZeroUsize::new(2).unwrap()));
        }
    };
    (MajorMinor, $variant:ident, $number:literal) => {
        paste! {
            pub const [< AA$number >]: Self =
                Self::$variant(MajorMinorIntervalQuality::Augmented(NonZeroUsize::new(2).unwrap()));
            pub const [< A$number >]: Self =
                Self::$variant(MajorMinorIntervalQuality::Augmented(NonZeroUsize::new(1).unwrap()));
            pub const [< M$number >]: Self =
                Self::$variant(MajorMinorIntervalQuality::Major);
            #[expect(non_upper_case_globals)]
            pub const [< m$number >]: Self =
                Self::$variant(MajorMinorIntervalQuality::Minor);
            #[expect(non_upper_case_globals)]
            pub const [< d$number >]: Self =
                Self::$variant(MajorMinorIntervalQuality::Diminished(NonZeroUsize::new(1).unwrap()));
            #[expect(non_upper_case_globals)]
            pub const [< dd$number >]: Self =
                Self::$variant(MajorMinorIntervalQuality::Diminished(NonZeroUsize::new(2).unwrap()));
        }
    };
}

impl UnorderedSimpleInterval {
    make_unordered_simple_interval_consts!(Perfect, Unison, 1);
    make_unordered_simple_interval_consts!(MajorMinor, Second, 2);
    make_unordered_simple_interval_consts!(MajorMinor, Third, 3);
    make_unordered_simple_interval_consts!(Perfect, Fourth, 4);
    make_unordered_simple_interval_consts!(Perfect, Fifth, 5);
    make_unordered_simple_interval_consts!(MajorMinor, Sixth, 6);
    make_unordered_simple_interval_consts!(MajorMinor, Seventh, 7);

    pub const fn interval_number(&self) -> UnorderedSimpleIntervalNumber {
        match self {
            Self::Unison(_) => UnorderedSimpleIntervalNumber::Unison,
            Self::Second(_) => UnorderedSimpleIntervalNumber::Second,
            Self::Third(_) => UnorderedSimpleIntervalNumber::Third,
            Self::Fourth(_) => UnorderedSimpleIntervalNumber::Fourth,
            Self::Fifth(_) => UnorderedSimpleIntervalNumber::Fifth,
            Self::Sixth(_) => UnorderedSimpleIntervalNumber::Sixth,
            Self::Seventh(_) => UnorderedSimpleIntervalNumber::Seventh,
        }
    }

    pub fn quality(&self) -> IntervalQuality {
        match self {
            Self::Unison(quality) | Self::Fourth(quality) | Self::Fifth(quality) => {
                (*quality).into()
            }
            Self::Second(quality)
            | Self::Third(quality)
            | Self::Sixth(quality)
            | Self::Seventh(quality) => (*quality).into(),
        }
    }

    pub const fn augment(self) -> Self {
        match self {
            Self::Unison(quality) => Self::Unison(quality.augment()),
            Self::Second(quality) => Self::Second(quality.augment()),
            Self::Third(quality) => Self::Third(quality.augment()),
            Self::Fourth(quality) => Self::Fourth(quality.augment()),
            Self::Fifth(quality) => Self::Fifth(quality.augment()),
            Self::Sixth(quality) => Self::Sixth(quality.augment()),
            Self::Seventh(quality) => Self::Seventh(quality.augment()),
        }
    }

    pub const fn diminish(self) -> Self {
        match self {
            Self::Unison(quality) => Self::Unison(quality.diminish()),
            Self::Second(quality) => Self::Second(quality.diminish()),
            Self::Third(quality) => Self::Third(quality.diminish()),
            Self::Fourth(quality) => Self::Fourth(quality.diminish()),
            Self::Fifth(quality) => Self::Fifth(quality.diminish()),
            Self::Sixth(quality) => Self::Sixth(quality.diminish()),
            Self::Seventh(quality) => Self::Seventh(quality.diminish()),
        }
    }

    pub fn checked_add(self, rhs: Self) -> Result<Self, ()> {
        let wrapping_add = self.wrapping_add(rhs);

        if wrapping_add.interval_number() < self.interval_number() {
            Err(())
        } else {
            Ok(wrapping_add)
        }
    }

    pub fn wrapping_add(self, rhs: Self) -> Self {
        let interval_number = self.interval_number().wrapping_add(rhs.interval_number());

        let goes_into_next_octave = interval_number < self.interval_number();

        let semitones_tet12 = self.semitones_tet12() + rhs.semitones_tet12()
            - if goes_into_next_octave { 12 } else { 0 };

        match interval_number {
            UnorderedSimpleIntervalNumber::Unison => {
                Self::Unison(PerfectIntervalQuality::from_index(semitones_tet12))
            }
            UnorderedSimpleIntervalNumber::Second => {
                Self::Second(MajorMinorIntervalQuality::from_index(semitones_tet12 - 1))
            }
            UnorderedSimpleIntervalNumber::Third => {
                Self::Third(MajorMinorIntervalQuality::from_index(semitones_tet12 - 3))
            }
            UnorderedSimpleIntervalNumber::Fourth => {
                Self::Fourth(PerfectIntervalQuality::from_index(semitones_tet12 - 5))
            }
            UnorderedSimpleIntervalNumber::Fifth => {
                Self::Fifth(PerfectIntervalQuality::from_index(semitones_tet12 - 7))
            }
            UnorderedSimpleIntervalNumber::Sixth => {
                Self::Sixth(MajorMinorIntervalQuality::from_index(semitones_tet12 - 8))
            }
            UnorderedSimpleIntervalNumber::Seventh => {
                Self::Seventh(MajorMinorIntervalQuality::from_index(semitones_tet12 - 10))
            }
        }
    }

    pub fn checked_sub(self, rhs: Self) -> Result<Self, ()> {
        let wrapping_sub = self.wrapping_sub(rhs);

        if wrapping_sub.interval_number() > self.interval_number() {
            Err(())
        } else {
            Ok(wrapping_sub)
        }
    }

    pub fn wrapping_sub(self, rhs: Self) -> Self {
        let interval_number = self.interval_number().wrapping_sub(rhs.interval_number());

        let goes_into_previous_octave = interval_number > self.interval_number();

        let semitones_tet12 = self.semitones_tet12() - rhs.semitones_tet12()
            + if goes_into_previous_octave { 12 } else { 0 };

        match interval_number {
            UnorderedSimpleIntervalNumber::Unison => {
                Self::Unison(PerfectIntervalQuality::from_index(semitones_tet12))
            }
            UnorderedSimpleIntervalNumber::Second => {
                Self::Second(MajorMinorIntervalQuality::from_index(semitones_tet12 - 1))
            }
            UnorderedSimpleIntervalNumber::Third => {
                Self::Third(MajorMinorIntervalQuality::from_index(semitones_tet12 - 3))
            }
            UnorderedSimpleIntervalNumber::Fourth => {
                Self::Fourth(PerfectIntervalQuality::from_index(semitones_tet12 - 5))
            }
            UnorderedSimpleIntervalNumber::Fifth => {
                Self::Fifth(PerfectIntervalQuality::from_index(semitones_tet12 - 7))
            }
            UnorderedSimpleIntervalNumber::Sixth => {
                Self::Sixth(MajorMinorIntervalQuality::from_index(semitones_tet12 - 8))
            }
            UnorderedSimpleIntervalNumber::Seventh => {
                Self::Seventh(MajorMinorIntervalQuality::from_index(semitones_tet12 - 10))
            }
        }
    }

    pub fn checked_mul(self, rhs: usize) -> Result<Self, ()> {
        let (wrapping_mul, extra_octaves) = self.wrapping_mul_with_octaves(rhs);

        if extra_octaves == 0 {
            Ok(wrapping_mul)
        } else {
            Err(())
        }
    }

    pub fn wrapping_mul(self, rhs: usize) -> Self {
        let (wrapping_mul, _) = self.wrapping_mul_with_octaves(rhs);

        wrapping_mul
    }

    fn wrapping_mul_with_octaves(self, rhs: usize) -> (Self, usize) {
        let (interval_number, extra_octaves) =
            self.interval_number().wrapping_mul_with_octaves(rhs);

        let semitones_tet12 = self.semitones_tet12() * rhs as isize - extra_octaves as isize * 12;

        let wrapping_mul = match interval_number {
            UnorderedSimpleIntervalNumber::Unison => {
                Self::Unison(PerfectIntervalQuality::from_index(semitones_tet12))
            }
            UnorderedSimpleIntervalNumber::Second => {
                Self::Second(MajorMinorIntervalQuality::from_index(semitones_tet12 - 1))
            }
            UnorderedSimpleIntervalNumber::Third => {
                Self::Third(MajorMinorIntervalQuality::from_index(semitones_tet12 - 3))
            }
            UnorderedSimpleIntervalNumber::Fourth => {
                Self::Fourth(PerfectIntervalQuality::from_index(semitones_tet12 - 5))
            }
            UnorderedSimpleIntervalNumber::Fifth => {
                Self::Fifth(PerfectIntervalQuality::from_index(semitones_tet12 - 7))
            }
            UnorderedSimpleIntervalNumber::Sixth => {
                Self::Sixth(MajorMinorIntervalQuality::from_index(semitones_tet12 - 8))
            }
            UnorderedSimpleIntervalNumber::Seventh => {
                Self::Seventh(MajorMinorIntervalQuality::from_index(semitones_tet12 - 10))
            }
        };

        (wrapping_mul, extra_octaves)
    }

    pub fn invert(self) -> Self {
        match self {
            Self::Unison(quality) => Self::Unison(quality.invert()),
            Self::Second(quality) => Self::Seventh(quality.invert()),
            Self::Third(quality) => Self::Sixth(quality.invert()),
            Self::Fourth(quality) => Self::Fifth(quality.invert()),
            Self::Fifth(quality) => Self::Fourth(quality.invert()),
            Self::Sixth(quality) => Self::Third(quality.invert()),
            Self::Seventh(quality) => Self::Second(quality.invert()),
        }
    }
}

impl Enharmonic for UnorderedSimpleInterval {
    fn enharmonic(&self, other: &Self) -> bool {
        TET12::semitones(self) == TET12::semitones(other)
    }
}

impl Display for UnorderedSimpleInterval {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.quality().fmt(f)?;

        if f.alternate() {
            " ".fmt(f)?;
        }

        self.interval_number().fmt(f)
    }
}

impl Add<UnorderedSimpleInterval> for Pitch {
    type Output = Self;

    fn add(self, rhs: UnorderedSimpleInterval) -> Self::Output {
        let Self { octave, class } = self;

        let octave = octave
            + (class.letter.index_within_octave() + rhs.interval_number().zero_based())
                .div_euclid(7) as isize;

        let class = self.class.wrapping_add(rhs);

        Self { octave, class }
    }
}

impl AddAssign<UnorderedSimpleInterval> for Pitch {
    fn add_assign(&mut self, rhs: UnorderedSimpleInterval) {
        *self = *self + rhs;
    }
}

impl Sub<UnorderedSimpleInterval> for Pitch {
    type Output = Self;

    fn sub(self, rhs: UnorderedSimpleInterval) -> Self::Output {
        let Self { octave, class } = self;

        let octave = octave
            + (class.letter.index_within_octave() as isize
                - rhs.interval_number().zero_based() as isize)
                .div_euclid(7);

        let class = self.class.wrapping_sub(rhs);

        Self { octave, class }
    }
}

impl SubAssign<UnorderedSimpleInterval> for Pitch {
    fn sub_assign(&mut self, rhs: UnorderedSimpleInterval) {
        *self = *self - rhs;
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UnorderedIntervalNumber {
    pub octaves: usize,
    pub simple: UnorderedSimpleIntervalNumber,
}

impl UnorderedIntervalNumber {
    pub const UNISON: Self = Self {
        octaves: 0,
        simple: UnorderedSimpleIntervalNumber::Unison,
    };

    pub const SECOND: Self = Self {
        octaves: 0,
        simple: UnorderedSimpleIntervalNumber::Second,
    };

    pub const THIRD: Self = Self {
        octaves: 0,
        simple: UnorderedSimpleIntervalNumber::Third,
    };

    pub const FOURTH: Self = Self {
        octaves: 0,
        simple: UnorderedSimpleIntervalNumber::Fourth,
    };

    pub const FIFTH: Self = Self {
        octaves: 0,
        simple: UnorderedSimpleIntervalNumber::Fifth,
    };

    pub const SIXTH: Self = Self {
        octaves: 0,
        simple: UnorderedSimpleIntervalNumber::Sixth,
    };

    pub const SEVENTH: Self = Self {
        octaves: 0,
        simple: UnorderedSimpleIntervalNumber::Seventh,
    };

    pub const OCTAVE: Self = Self {
        octaves: 1,
        simple: UnorderedSimpleIntervalNumber::Unison,
    };

    pub const NINTH: Self = Self {
        octaves: 1,
        simple: UnorderedSimpleIntervalNumber::Second,
    };

    pub const TENTH: Self = Self {
        octaves: 1,
        simple: UnorderedSimpleIntervalNumber::Third,
    };

    pub const ELEVENTH: Self = Self {
        octaves: 1,
        simple: UnorderedSimpleIntervalNumber::Fourth,
    };

    pub const TWELFTH: Self = Self {
        octaves: 1,
        simple: UnorderedSimpleIntervalNumber::Fifth,
    };

    pub const THIRTEENTH: Self = Self {
        octaves: 1,
        simple: UnorderedSimpleIntervalNumber::Sixth,
    };

    pub const FOURTEENTH: Self = Self {
        octaves: 1,
        simple: UnorderedSimpleIntervalNumber::Seventh,
    };

    pub const DOUBLE_OCTAVE: Self = Self {
        octaves: 2,
        simple: UnorderedSimpleIntervalNumber::Unison,
    };

    pub fn zero_based(&self) -> usize {
        let Self { octaves, simple } = self;

        octaves * 7 + simple.zero_based()
    }

    pub fn one_based(&self) -> usize {
        self.zero_based() + 1
    }

    pub fn from_zero_based(number: usize) -> Self {
        Self {
            octaves: number / 7,
            simple: UnorderedSimpleIntervalNumber::try_from_zero_based(number % 7)
                .expect("number should be in valid range"),
        }
    }

    pub fn try_from_one_based(number: usize) -> Result<Self, ()> {
        match number {
            0 => Err(()),
            _ => Ok(Self::from_zero_based(number - 1)),
        }
    }

    pub const fn ascending(self) -> OrderedIntervalNumber {
        OrderedIntervalNumber {
            direction: IntervalDirection::Ascending,
            unordered: self,
        }
    }

    pub const fn descending(self) -> OrderedIntervalNumber {
        OrderedIntervalNumber {
            direction: IntervalDirection::Descending,
            unordered: self,
        }
    }

    pub fn is_simple(&self) -> bool {
        self.octaves == 0
    }

    pub fn is_compound(&self) -> bool {
        !self.is_simple()
    }

    pub fn checked_sub(self, rhs: Self) -> Result<Self, ()> {
        let simple = self.simple.wrapping_sub(rhs.simple);

        let goes_into_previous_octave = simple > self.simple;

        let octaves = self
            .octaves
            .checked_sub(rhs.octaves + if goes_into_previous_octave { 1 } else { 0 })
            .ok_or(())?;

        Ok(Self { octaves, simple })
    }
}

impl From<UnorderedSimpleIntervalNumber> for UnorderedIntervalNumber {
    fn from(simple: UnorderedSimpleIntervalNumber) -> Self {
        Self { octaves: 0, simple }
    }
}

impl Display for UnorderedIntervalNumber {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            if self.zero_based() % 7 == 0 {
                match self.octaves {
                    0 => write!(f, "unison"),
                    1 => write!(f, "octave"),
                    2 => write!(f, "double octave"),
                    octaves => write!(f, "{octaves}x octave"),
                }
            } else {
                write!(
                    f,
                    "{}",
                    Num2Words::new(self.one_based() as u32)
                        .ordinal()
                        .to_words()
                        .expect("ordinal formatting should succeed")
                )
            }
        } else {
            write!(f, "{}", self.one_based())
        }
    }
}

impl Add for UnorderedIntervalNumber {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let simple = self.simple.wrapping_add(rhs.simple);

        let goes_into_next_octave = simple < self.simple;

        let octaves = self.octaves + rhs.octaves + if goes_into_next_octave { 1 } else { 0 };

        Self { octaves, simple }
    }
}

impl AddAssign for UnorderedIntervalNumber {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Sub for UnorderedIntervalNumber {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.checked_sub(rhs)
            .expect("attempted to subtract larger interval from smaller interval")
    }
}

impl SubAssign for UnorderedIntervalNumber {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl Mul<usize> for UnorderedIntervalNumber {
    type Output = Self;

    fn mul(self, rhs: usize) -> Self::Output {
        let (simple, extra_octaves) = self.simple.wrapping_mul_with_octaves(rhs);

        let octaves = self.octaves * rhs + extra_octaves;

        Self { octaves, simple }
    }
}

impl Mul<UnorderedIntervalNumber> for usize {
    type Output = UnorderedIntervalNumber;

    fn mul(self, rhs: UnorderedIntervalNumber) -> Self::Output {
        rhs * self
    }
}

impl MulAssign<usize> for UnorderedIntervalNumber {
    fn mul_assign(&mut self, rhs: usize) {
        *self = *self * rhs;
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UnorderedInterval {
    pub octaves: usize,
    pub simple: UnorderedSimpleInterval,
}

macro_rules! make_unordered_interval_consts {
    (Perfect, $number:literal, $simple:literal, $octaves:literal) => {
        paste! {
            pub const [< AA$number >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimpleInterval::[< AA$simple >],
            };
            pub const [< A$number >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimpleInterval::[< A$simple >],
            };
            pub const [< P$number >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimpleInterval::[< P$simple >],
            };
            #[expect(non_upper_case_globals)]
            pub const [< d$number >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimpleInterval::[< d$simple >],
            };
            #[expect(non_upper_case_globals)]
            pub const [< dd$number >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimpleInterval::[< dd$simple >],
            };
        }
    };
    (MajorMinor, $number:literal, $simple:literal, $octaves:literal) => {
        paste! {
            pub const [< AA$number >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimpleInterval::[< AA$simple >],
            };
            pub const [< A$number >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimpleInterval::[< A$simple >],
            };
            pub const [< M$number >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimpleInterval::[< M$simple >],
            };
            #[expect(non_upper_case_globals)]
            pub const [< m$number >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimpleInterval::[< m$simple >],
            };
            #[expect(non_upper_case_globals)]
            pub const [< d$number >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimpleInterval::[< d$simple >],
            };
            #[expect(non_upper_case_globals)]
            pub const [< dd$number >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimpleInterval::[< dd$simple >],
            };
        }
    };
}

impl UnorderedInterval {
    make_unordered_interval_consts!(Perfect, 1, 1, 0);
    make_unordered_interval_consts!(MajorMinor, 2, 2, 0);
    make_unordered_interval_consts!(MajorMinor, 3, 3, 0);
    make_unordered_interval_consts!(Perfect, 4, 4, 0);
    make_unordered_interval_consts!(Perfect, 5, 5, 0);
    make_unordered_interval_consts!(MajorMinor, 6, 6, 0);
    make_unordered_interval_consts!(MajorMinor, 7, 7, 0);

    make_unordered_interval_consts!(Perfect, 8, 1, 1);
    make_unordered_interval_consts!(MajorMinor, 9, 2, 1);
    make_unordered_interval_consts!(MajorMinor, 10, 3, 1);
    make_unordered_interval_consts!(Perfect, 11, 4, 1);
    make_unordered_interval_consts!(Perfect, 12, 5, 1);
    make_unordered_interval_consts!(MajorMinor, 13, 6, 1);
    make_unordered_interval_consts!(MajorMinor, 14, 7, 1);
    make_unordered_interval_consts!(Perfect, 15, 1, 2);

    pub const fn interval_number(&self) -> UnorderedIntervalNumber {
        let Self { octaves, simple } = self;

        UnorderedIntervalNumber {
            octaves: *octaves,
            simple: simple.interval_number(),
        }
    }

    pub fn quality(&self) -> IntervalQuality {
        self.simple.quality()
    }

    pub const fn ascending(self) -> OrderedInterval {
        OrderedInterval {
            direction: IntervalDirection::Ascending,
            unordered: self,
        }
    }

    pub const fn descending(self) -> OrderedInterval {
        OrderedInterval {
            direction: IntervalDirection::Descending,
            unordered: self,
        }
    }

    pub const fn augment(self) -> Self {
        let Self { octaves, simple } = self;

        Self {
            octaves,
            simple: simple.augment(),
        }
    }

    pub const fn diminish(self) -> Self {
        let Self { octaves, simple } = self;

        Self {
            octaves,
            simple: simple.diminish(),
        }
    }

    pub fn is_simple(&self) -> bool {
        self.octaves == 0
    }

    pub fn is_compound(&self) -> bool {
        !self.is_simple()
    }

    pub fn checked_sub(self, rhs: Self) -> Result<Self, ()> {
        let simple = self.simple.wrapping_sub(rhs.simple);

        let goes_into_previous_octave = simple.interval_number() > self.simple.interval_number();

        let octaves = self
            .octaves
            .checked_sub(rhs.octaves + if goes_into_previous_octave { 1 } else { 0 })
            .ok_or(())?;

        Ok(Self { octaves, simple })
    }
}

impl Enharmonic for UnorderedInterval {
    fn enharmonic(&self, other: &Self) -> bool {
        TET12::semitones(self) == TET12::semitones(other)
    }
}

impl From<UnorderedSimpleInterval> for UnorderedInterval {
    fn from(simple: UnorderedSimpleInterval) -> Self {
        Self { octaves: 0, simple }
    }
}

impl Display for UnorderedInterval {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.quality().fmt(f)?;

        if f.alternate() {
            " ".fmt(f)?;
        }

        self.interval_number().fmt(f)
    }
}

impl Add<UnorderedInterval> for Pitch {
    type Output = Self;

    fn add(self, rhs: UnorderedInterval) -> Self::Output {
        let UnorderedInterval { octaves, simple } = rhs;

        let Self { octave, class } = self + simple;

        Self {
            octave: octave + octaves as isize,
            class,
        }
    }
}

impl AddAssign<UnorderedInterval> for Pitch {
    fn add_assign(&mut self, rhs: UnorderedInterval) {
        *self = *self + rhs;
    }
}

impl Sub<UnorderedInterval> for Pitch {
    type Output = Self;

    fn sub(self, rhs: UnorderedInterval) -> Self::Output {
        let UnorderedInterval { octaves, simple } = rhs;

        let Self { octave, class } = self - simple;

        Self {
            octave: octave - octaves as isize,
            class,
        }
    }
}

impl SubAssign<UnorderedInterval> for Pitch {
    fn sub_assign(&mut self, rhs: UnorderedInterval) {
        *self = *self - rhs;
    }
}

impl Add for UnorderedInterval {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let simple = self.simple.wrapping_add(rhs.simple);

        let goes_into_next_octave = simple.interval_number() < self.simple.interval_number();

        let octaves = self.octaves + rhs.octaves + if goes_into_next_octave { 1 } else { 0 };

        Self { octaves, simple }
    }
}

impl AddAssign for UnorderedInterval {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Sub for UnorderedInterval {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.checked_sub(rhs)
            .expect("attempted to subtract larger interval from smaller interval")
    }
}

impl SubAssign for UnorderedInterval {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl Mul<usize> for UnorderedInterval {
    type Output = Self;

    fn mul(self, rhs: usize) -> Self::Output {
        let (simple, extra_octaves) = self.simple.wrapping_mul_with_octaves(rhs);

        let octaves = self.octaves * rhs + extra_octaves;

        Self { octaves, simple }
    }
}

impl Mul<UnorderedInterval> for usize {
    type Output = UnorderedInterval;

    fn mul(self, rhs: UnorderedInterval) -> Self::Output {
        rhs * self
    }
}

impl MulAssign<usize> for UnorderedInterval {
    fn mul_assign(&mut self, rhs: usize) {
        *self = *self * rhs;
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntervalDirection {
    Descending,
    Ascending,
}

impl IntervalDirection {
    pub fn sign(&self) -> isize {
        match self {
            Self::Descending => -1,
            Self::Ascending => 1,
        }
    }
}

impl Display for IntervalDirection {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            match self {
                Self::Descending => write!(f, "descending"),
                Self::Ascending => write!(f, "ascending"),
            }
        } else {
            match self {
                Self::Descending => write!(f, "-"),
                Self::Ascending => write!(f, "+"),
            }
        }
    }
}

impl Neg for IntervalDirection {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            IntervalDirection::Ascending => IntervalDirection::Descending,
            IntervalDirection::Descending => IntervalDirection::Ascending,
        }
    }
}

#[derive(Debug, Clone, Copy, Hash)]
pub struct OrderedIntervalNumber {
    pub direction: IntervalDirection,
    pub unordered: UnorderedIntervalNumber,
}

impl OrderedIntervalNumber {
    pub fn is_simple(&self) -> bool {
        self.unordered.is_simple()
    }

    pub fn is_compound(&self) -> bool {
        self.unordered.is_compound()
    }
}

impl Display for OrderedIntervalNumber {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            direction,
            unordered,
        } = self;

        direction.fmt(f)?;

        if f.alternate() {
            " ".fmt(f)?;
        }

        unordered.fmt(f)
    }
}

impl Add for OrderedIntervalNumber {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        if self.unordered >= rhs.unordered {
            (self.unordered - rhs.unordered).ascending()
        } else {
            (rhs.unordered - self.unordered).descending()
        }
    }
}

impl AddAssign for OrderedIntervalNumber {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Sub for OrderedIntervalNumber {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self + (-rhs)
    }
}

impl SubAssign for OrderedIntervalNumber {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl Neg for OrderedIntervalNumber {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let Self {
            direction,
            unordered,
        } = self;

        Self {
            direction: -direction,
            unordered,
        }
    }
}

impl Mul<isize> for OrderedIntervalNumber {
    type Output = Self;

    fn mul(self, rhs: isize) -> Self::Output {
        let Self {
            direction,
            unordered,
        } = self;

        if rhs >= 0 {
            Self {
                direction,
                unordered: unordered * rhs as usize,
            }
        } else {
            Self {
                direction,
                unordered: unordered * (-rhs as usize),
            }
        }
    }
}

impl Mul<OrderedIntervalNumber> for isize {
    type Output = OrderedIntervalNumber;

    fn mul(self, rhs: OrderedIntervalNumber) -> Self::Output {
        rhs * self
    }
}

impl MulAssign<isize> for OrderedIntervalNumber {
    fn mul_assign(&mut self, rhs: isize) {
        *self = *self * rhs;
    }
}

#[derive(Debug, Clone, Copy, Eq)]
pub struct OrderedInterval {
    pub direction: IntervalDirection,
    pub unordered: UnorderedInterval,
}

impl OrderedInterval {
    pub const fn interval_number(&self) -> OrderedIntervalNumber {
        let Self {
            direction,
            unordered,
        } = self;

        OrderedIntervalNumber {
            direction: *direction,
            unordered: unordered.interval_number(),
        }
    }

    pub fn quality(&self) -> IntervalQuality {
        self.unordered.quality()
    }

    pub fn is_simple(&self) -> bool {
        self.unordered.is_simple()
    }

    pub fn is_compound(&self) -> bool {
        self.unordered.is_compound()
    }

    pub const fn augment(self) -> Self {
        let Self {
            direction,
            unordered,
        } = self;

        Self {
            direction,
            unordered: unordered.augment(),
        }
    }

    pub const fn diminish(self) -> Self {
        let Self {
            direction,
            unordered,
        } = self;

        Self {
            direction,
            unordered: unordered.diminish(),
        }
    }
}

impl PartialEq for OrderedInterval {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Self {
                    direction,
                    unordered:
                        UnorderedInterval {
                            octaves: 0,
                            simple: UnorderedSimpleInterval::Unison(unison_quality),
                        },
                },
                Self {
                    direction: other_direction,
                    unordered:
                        UnorderedInterval {
                            octaves: 0,
                            simple: UnorderedSimpleInterval::Unison(other_unison_quality),
                        },
                },
            ) => {
                (direction == other_direction && unison_quality == other_unison_quality)
                    || (direction == &-*other_direction
                        && unison_quality == &other_unison_quality.invert())
            }
            (
                Self {
                    direction,
                    unordered,
                },
                Self {
                    direction: other_direction,
                    unordered: other_unordered,
                },
            ) => direction == other_direction && unordered == other_unordered,
        }
    }
}

impl PartialOrd for OrderedInterval {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OrderedInterval {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (
                Self {
                    direction,
                    unordered:
                        UnorderedInterval {
                            octaves: 0,
                            simple: UnorderedSimpleInterval::Unison(unison_quality),
                        },
                },
                Self {
                    direction: other_direction,
                    unordered:
                        UnorderedInterval {
                            octaves: 0,
                            simple: UnorderedSimpleInterval::Unison(other_unison_quality),
                        },
                },
            ) => match (direction, other_direction) {
                (IntervalDirection::Descending, IntervalDirection::Ascending) => {
                    unison_quality.invert().cmp(other_unison_quality)
                }
                (IntervalDirection::Ascending, IntervalDirection::Descending) => {
                    unison_quality.cmp(&other_unison_quality.invert())
                }
                (IntervalDirection::Descending, IntervalDirection::Descending) => {
                    other_unison_quality.cmp(unison_quality)
                }
                (IntervalDirection::Ascending, IntervalDirection::Ascending) => {
                    unison_quality.cmp(other_unison_quality)
                }
            },
            (
                Self {
                    direction,
                    unordered,
                },
                Self {
                    direction: other_direction,
                    unordered: other_unordered,
                },
            ) => match (direction, other_direction) {
                (IntervalDirection::Descending, IntervalDirection::Ascending) => {
                    std::cmp::Ordering::Less
                }
                (IntervalDirection::Ascending, IntervalDirection::Descending) => {
                    std::cmp::Ordering::Greater
                }
                (IntervalDirection::Descending, IntervalDirection::Descending) => {
                    other_unordered.cmp(unordered)
                }
                (IntervalDirection::Ascending, IntervalDirection::Ascending) => {
                    unordered.cmp(other_unordered)
                }
            },
        }
    }
}

impl Enharmonic for OrderedInterval {
    fn enharmonic(&self, other: &Self) -> bool {
        TET12::semitones(self) == TET12::semitones(other)
    }
}

impl Display for OrderedInterval {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self {
                direction: _,
                unordered: UnorderedInterval::P1,
            } => UnorderedInterval::P1.fmt(f),
            Self {
                direction,
                unordered,
            } => {
                if f.alternate() {
                    write!(f, "{:#} {:#}", direction, unordered)
                } else {
                    write!(f, "{}{}", direction, unordered)
                }
            }
        }
    }
}

impl Add<OrderedInterval> for Pitch {
    type Output = Self;

    fn add(self, rhs: OrderedInterval) -> Self::Output {
        let OrderedInterval {
            direction,
            unordered,
        } = rhs;

        match direction {
            IntervalDirection::Descending => self - unordered,
            IntervalDirection::Ascending => self + unordered,
        }
    }
}

impl AddAssign<OrderedInterval> for Pitch {
    fn add_assign(&mut self, rhs: OrderedInterval) {
        *self = *self + rhs;
    }
}

impl Sub<OrderedInterval> for Pitch {
    type Output = Self;

    fn sub(self, rhs: OrderedInterval) -> Self::Output {
        let OrderedInterval {
            direction,
            unordered,
        } = rhs;

        match direction {
            IntervalDirection::Descending => self + unordered,
            IntervalDirection::Ascending => self - unordered,
        }
    }
}

impl SubAssign<OrderedInterval> for Pitch {
    fn sub_assign(&mut self, rhs: OrderedInterval) {
        *self = *self - rhs;
    }
}

impl Add for OrderedInterval {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match (self.direction, rhs.direction) {
            (IntervalDirection::Descending, IntervalDirection::Descending) => {
                (self.unordered + rhs.unordered).descending()
            }
            (IntervalDirection::Descending, IntervalDirection::Ascending) => {
                if rhs.unordered >= self.unordered {
                    (rhs.unordered - self.unordered).ascending()
                } else {
                    (self.unordered - rhs.unordered).descending()
                }
            }
            (IntervalDirection::Ascending, IntervalDirection::Descending) => {
                if self.unordered >= rhs.unordered {
                    (self.unordered - rhs.unordered).ascending()
                } else {
                    (rhs.unordered - self.unordered).descending()
                }
            }
            (IntervalDirection::Ascending, IntervalDirection::Ascending) => {
                (self.unordered + rhs.unordered).ascending()
            }
        }
    }
}

impl AddAssign for OrderedInterval {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Sub for OrderedInterval {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self + (-rhs)
    }
}

impl SubAssign for OrderedInterval {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl Neg for OrderedInterval {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let Self {
            direction,
            unordered,
        } = self;

        Self {
            direction: -direction,
            unordered,
        }
    }
}

impl Mul<isize> for OrderedInterval {
    type Output = Self;

    fn mul(self, rhs: isize) -> Self::Output {
        let Self {
            direction,
            unordered,
        } = self;

        if rhs >= 0 {
            Self {
                direction,
                unordered: unordered * rhs as usize,
            }
        } else {
            Self {
                direction: -direction,
                unordered: unordered * (-rhs as usize),
            }
        }
    }
}

impl Mul<OrderedInterval> for isize {
    type Output = OrderedInterval;

    fn mul(self, rhs: OrderedInterval) -> Self::Output {
        rhs * self
    }
}

impl MulAssign<isize> for OrderedInterval {
    fn mul_assign(&mut self, rhs: isize) {
        *self = *self * rhs;
    }
}

#[cfg(test)]
mod tests {
    use quickcheck_macros::quickcheck;

    use crate::{
        enharmonic::{assert_enharmonic, assert_not_enharmonic},
        pitches::Pitch,
    };

    use super::*;

    #[test]
    fn interval_number_ordering_examples() {
        assert!(UnorderedIntervalNumber::UNISON < UnorderedIntervalNumber::SECOND);
        assert!(UnorderedIntervalNumber::THIRD < UnorderedIntervalNumber::SEVENTH);
        assert!(UnorderedIntervalNumber::UNISON < UnorderedIntervalNumber::OCTAVE);
        assert!(UnorderedIntervalNumber::THIRD < UnorderedIntervalNumber::NINTH);
    }

    #[test]
    fn interval_from_one_based_examples() {
        assert_eq!(UnorderedIntervalNumber::try_from_one_based(0), Err(()));

        assert_eq!(
            UnorderedIntervalNumber::try_from_one_based(1),
            Ok(UnorderedIntervalNumber::UNISON)
        );

        assert_eq!(
            UnorderedIntervalNumber::try_from_one_based(4),
            Ok(UnorderedIntervalNumber::FOURTH)
        );

        assert_eq!(
            UnorderedIntervalNumber::try_from_one_based(8),
            Ok(UnorderedIntervalNumber::OCTAVE)
        );

        assert_eq!(
            UnorderedIntervalNumber::try_from_one_based(13),
            Ok(UnorderedIntervalNumber::THIRTEENTH)
        );
    }

    #[test]
    fn ordered_interval_unison_equality_examples() {
        assert_eq!(
            UnorderedInterval::P1.ascending(),
            UnorderedInterval::P1.ascending()
        );
        assert_eq!(
            UnorderedInterval::P1.ascending(),
            UnorderedInterval::P1.descending()
        );
        assert_eq!(
            UnorderedInterval::P1.descending(),
            UnorderedInterval::P1.ascending()
        );
        assert_eq!(
            UnorderedInterval::P1.descending(),
            UnorderedInterval::P1.descending()
        );

        assert_eq!(
            UnorderedInterval::A1.ascending(),
            UnorderedInterval::d1.descending()
        );
        assert_eq!(
            UnorderedInterval::A1.descending(),
            UnorderedInterval::d1.ascending()
        );
        assert_ne!(
            UnorderedInterval::A1.ascending(),
            UnorderedInterval::d1.ascending()
        );
        assert_ne!(
            UnorderedInterval::A1.descending(),
            UnorderedInterval::d1.descending()
        );
    }

    #[test]
    fn ordered_interval_ordering_examples() {
        assert_eq!(
            UnorderedInterval::P1
                .ascending()
                .cmp(&UnorderedInterval::P1.ascending()),
            std::cmp::Ordering::Equal,
        );
        assert_eq!(
            UnorderedInterval::d1
                .ascending()
                .cmp(&UnorderedInterval::P1.ascending()),
            std::cmp::Ordering::Less,
        );
        assert_eq!(
            UnorderedInterval::d1
                .ascending()
                .cmp(&UnorderedInterval::A1.ascending()),
            std::cmp::Ordering::Less,
        );
        assert_eq!(
            UnorderedInterval::d1
                .descending()
                .cmp(&UnorderedInterval::A1.ascending()),
            std::cmp::Ordering::Equal,
        );
        assert_eq!(
            UnorderedInterval::d1
                .descending()
                .cmp(&UnorderedInterval::A1.descending()),
            std::cmp::Ordering::Greater,
        );

        assert_eq!(
            UnorderedInterval::M2
                .descending()
                .cmp(&UnorderedInterval::P1.ascending()),
            std::cmp::Ordering::Less,
        );
        assert_eq!(
            UnorderedInterval::M2
                .descending()
                .cmp(&UnorderedInterval::M2.ascending()),
            std::cmp::Ordering::Less,
        );

        assert_eq!(
            UnorderedInterval::M2
                .ascending()
                .cmp(&UnorderedInterval::m3.ascending()),
            std::cmp::Ordering::Less,
        );
        assert_eq!(
            UnorderedInterval::A5
                .ascending()
                .cmp(&UnorderedInterval::m6.ascending()),
            std::cmp::Ordering::Less,
        );
        assert_eq!(
            UnorderedInterval::A5
                .ascending()
                .cmp(&UnorderedInterval::d6.ascending()),
            std::cmp::Ordering::Less,
        );

        assert_eq!(
            UnorderedInterval::M3
                .descending()
                .cmp(&UnorderedInterval::P5.descending()),
            std::cmp::Ordering::Greater,
        );
        assert_eq!(
            UnorderedInterval::M3
                .descending()
                .cmp(&UnorderedInterval::AA4.descending()),
            std::cmp::Ordering::Greater,
        );
    }

    #[quickcheck]
    fn ordered_interval_ordering_respects_negation(a: OrderedInterval, b: OrderedInterval) {
        assert_eq!((-a).cmp(&-b), a.cmp(&b).reverse());
    }

    #[quickcheck]
    fn ordered_interval_eq_agrees_with_ord(a: OrderedInterval, b: OrderedInterval) {
        assert_eq!(a == b, a.cmp(&b) == std::cmp::Ordering::Equal);
    }

    #[test]
    fn ordered_interval_display_examples() {
        assert_eq!(format!("{}", UnorderedInterval::P1.ascending()), "P1");

        assert_eq!(format!("{}", UnorderedInterval::M9.ascending()), "+M9");

        assert_eq!(format!("{}", UnorderedInterval::m7.descending()), "-m7");

        assert_eq!(format!("{}", UnorderedInterval::A5.descending()), "-A5");

        assert_eq!(format!("{}", UnorderedInterval::dd11.ascending()), "+dd11");

        assert_eq!(
            format!("{:#}", UnorderedInterval::A1.ascending()),
            "ascending augmented unison"
        );

        assert_eq!(
            format!("{:#}", UnorderedInterval::P8.ascending()),
            "ascending perfect octave"
        );

        assert_eq!(
            format!("{:#}", UnorderedInterval::A8.ascending()),
            "ascending augmented octave"
        );

        assert_eq!(
            format!("{:#}", UnorderedInterval::P15.descending()),
            "descending perfect double octave"
        );

        assert_eq!(
            format!(
                "{:#}",
                UnorderedInterval {
                    octaves: 3,
                    simple: UnorderedSimpleInterval::d1
                }
                .ascending()
            ),
            "ascending diminished 3x octave"
        );

        assert_eq!(
            format!("{:#}", UnorderedInterval::M3.descending()),
            "descending major third"
        );

        assert_eq!(
            format!("{:#}", UnorderedInterval::m9.descending()),
            "descending minor ninth"
        );

        assert_eq!(
            format!("{:#}", UnorderedInterval::AA5.ascending()),
            "ascending doubly augmented fifth"
        );

        assert_eq!(
            format!(
                "{:#}",
                UnorderedInterval::dd2.diminish().diminish().descending()
            ),
            "descending 4x diminished second"
        );
    }

    #[quickcheck]
    fn ordered_interval_enharmonic_examples() {
        assert_enharmonic!(
            UnorderedInterval::P1.ascending(),
            UnorderedInterval::P1.ascending()
        );

        assert_enharmonic!(
            UnorderedInterval::A3.ascending(),
            UnorderedInterval::P4.ascending()
        );

        assert_enharmonic!(
            UnorderedInterval::dd2.ascending(),
            UnorderedInterval::m2.descending()
        );

        assert_enharmonic!(
            UnorderedInterval::A4.descending(),
            UnorderedInterval::d5.descending()
        );

        assert_enharmonic!(
            UnorderedInterval::AA7.ascending(),
            UnorderedInterval::A8.ascending()
        );

        assert_not_enharmonic!(
            UnorderedInterval::P1.ascending(),
            UnorderedInterval::P8.ascending()
        );

        assert_not_enharmonic!(
            UnorderedInterval::M3.ascending(),
            UnorderedInterval::M3.descending()
        );
    }

    #[quickcheck]
    fn ordered_interval_enharmonic_to_self(interval: OrderedInterval) {
        assert_enharmonic!(interval, interval);
    }

    #[quickcheck]
    fn ordered_interval_eq_implies_enharmonic(a: OrderedInterval, b: OrderedInterval) {
        if a == b {
            assert_enharmonic!(a, b);
        }
    }

    #[quickcheck]
    fn ordered_interval_enharmonic_augment_invariant(a: OrderedInterval, b: OrderedInterval) {
        match (a.direction, b.direction) {
            (IntervalDirection::Descending, IntervalDirection::Descending)
            | (IntervalDirection::Ascending, IntervalDirection::Ascending) => {
                assert_eq!(a.enharmonic(&b), a.augment().enharmonic(&b.augment()));
            }
            (IntervalDirection::Descending, IntervalDirection::Ascending) => {
                assert_eq!(a.enharmonic(&b), a.diminish().enharmonic(&b.augment()));
            }
            (IntervalDirection::Ascending, IntervalDirection::Descending) => {
                assert_eq!(a.enharmonic(&b), a.augment().enharmonic(&b.diminish()));
            }
        }
    }

    #[quickcheck]
    fn ordered_interval_enharmonic_diminish_invariant(a: OrderedInterval, b: OrderedInterval) {
        match (a.direction, b.direction) {
            (IntervalDirection::Descending, IntervalDirection::Descending)
            | (IntervalDirection::Ascending, IntervalDirection::Ascending) => {
                assert_eq!(a.enharmonic(&b), a.diminish().enharmonic(&b.diminish()));
            }
            (IntervalDirection::Descending, IntervalDirection::Ascending) => {
                assert_eq!(a.enharmonic(&b), a.augment().enharmonic(&b.diminish()));
            }
            (IntervalDirection::Ascending, IntervalDirection::Descending) => {
                assert_eq!(a.enharmonic(&b), a.diminish().enharmonic(&b.augment()));
            }
        }
    }

    #[quickcheck]
    fn pitch_sub_preserves_enharmonic_equivalence(a1: Pitch, a2: Pitch, b1: Pitch, b2: Pitch) {
        match (a1.enharmonic(&a2), b1.enharmonic(&b2)) {
            (true, true) => {
                assert_enharmonic!(a1 - b1, a2 - b2);
            }
            (true, false) | (false, true) => {
                assert_not_enharmonic!(a1 - b1, a2 - b2);
            }
            (false, false) => {}
        }
    }

    #[test]
    fn pitch_add_ordered_pitch_interval_examples() {
        assert_eq!(Pitch::C4 + UnorderedInterval::M3.ascending(), Pitch::E4);

        assert_eq!(Pitch::C4 + UnorderedInterval::m2.ascending(), Pitch::Db4);

        assert_eq!(Pitch::E4 + UnorderedInterval::m2.ascending(), Pitch::F4);

        assert_eq!(Pitch::A4 + UnorderedInterval::m3.ascending(), Pitch::C5);

        assert_eq!(Pitch::G2 + UnorderedInterval::A12.ascending(), Pitch::Ds4);

        assert_eq!(Pitch::C3 + UnorderedInterval::M2.descending(), Pitch::Bb2);

        assert_eq!(Pitch::E6 + UnorderedInterval::M3.descending(), Pitch::C6);

        assert_eq!(Pitch::Fb3 + UnorderedInterval::dd9.descending(), Pitch::Es2);
    }

    #[quickcheck]
    fn pitch_add_ordered_interval_equals_sub_neg(pitch: Pitch, interval: OrderedInterval) {
        assert_eq!(pitch + interval, pitch - (-interval));
    }

    #[quickcheck]
    fn pitch_sub_ordered_interval_equals_addneg(pitch: Pitch, interval: OrderedInterval) {
        assert_eq!(pitch - interval, pitch + (-interval));
    }

    #[quickcheck]
    fn pitch_add_and_sub_ordered_interval_are_inverses(pitch: Pitch, interval: OrderedInterval) {
        assert_eq!((pitch + interval) - interval, pitch);
        assert_eq!((pitch - interval) + interval, pitch);
    }

    #[quickcheck]
    fn pitch_add_unison(pitch: Pitch) {
        assert_eq!(pitch + UnorderedInterval::P1, pitch);
        assert_eq!(pitch + UnorderedInterval::P1.ascending(), pitch);
        assert_eq!(pitch + UnorderedInterval::P1.descending(), pitch);
    }

    #[quickcheck]
    fn pitch_sub_unison(pitch: Pitch) {
        assert_eq!(pitch - UnorderedInterval::P1, pitch);
        assert_eq!(pitch - UnorderedInterval::P1.ascending(), pitch);
        assert_eq!(pitch - UnorderedInterval::P1.descending(), pitch);
    }

    #[quickcheck]
    fn pitch_addoctave(pitch: Pitch) {
        assert_eq!(pitch + UnorderedInterval::P8, pitch.octave_up());
    }

    #[quickcheck]
    fn pitch_sub_octave(pitch: Pitch) {
        assert_eq!(pitch - UnorderedInterval::P8, pitch.octave_down());
    }

    #[quickcheck]
    fn pitch_add_ordered_interval_semitones_tet12(pitch: Pitch, interval: OrderedInterval) {
        assert_eq!(
            (pitch + interval).semitones_tet12(),
            pitch.semitones_tet12() + interval.semitones_tet12()
        );
    }

    #[quickcheck]
    fn pitch_add_ordered_interval_preserves_enharmonic_equivalence(
        pitch_1: Pitch,
        pitch_2: Pitch,
        interval_1: OrderedInterval,
        interval_2: OrderedInterval,
    ) {
        match (
            pitch_1.enharmonic(&pitch_2),
            interval_1.enharmonic(&interval_2),
        ) {
            (true, true) => {
                assert_enharmonic!(pitch_1 + interval_1, pitch_2 + interval_2);
            }
            (true, false) | (false, true) => {
                assert_not_enharmonic!(pitch_1 + interval_1, pitch_2 + interval_2);
            }
            (false, false) => {}
        }
    }

    #[test]
    fn add_unordered_interval_examples() {
        assert_eq!(
            UnorderedInterval::M3 + UnorderedInterval::m3,
            UnorderedInterval::P5
        );

        assert_eq!(
            UnorderedInterval::P5 + UnorderedInterval::P4,
            UnorderedInterval::P8
        );

        assert_eq!(
            UnorderedInterval::d6 + UnorderedInterval::AA5,
            UnorderedInterval::M10
        );
    }

    #[test]
    fn sub_unordered_interval_examples() {
        assert_eq!(
            UnorderedInterval::P5 - UnorderedInterval::m3,
            UnorderedInterval::M3
        );

        assert_eq!(
            UnorderedInterval::P1 - UnorderedInterval::A1,
            UnorderedInterval::d1
        );
    }

    #[quickcheck]
    fn add_unordered_interval_semitones_tet12(a: UnorderedInterval, b: UnorderedInterval) {
        assert_eq!(
            (a + b).semitones_tet12(),
            a.semitones_tet12() + b.semitones_tet12()
        );
    }

    #[quickcheck]
    fn sub_unordered_interval_semitones_tet12(a: UnorderedInterval, b: UnorderedInterval) {
        if let Ok(sub) = a.checked_sub(b) {
            assert_eq!(
                sub.semitones_tet12(),
                a.semitones_tet12() - b.semitones_tet12()
            );
        }
    }

    #[quickcheck]
    fn add_unordered_interval_preserves_enharmonic_equivalence(
        a: UnorderedInterval,
        b: UnorderedInterval,
        c: UnorderedInterval,
        d: UnorderedInterval,
    ) {
        match (a.enharmonic(&b), c.enharmonic(&d)) {
            (true, true) => {
                assert_enharmonic!(a + b, c + d);
            }
            (true, false) | (false, true) => {
                assert_not_enharmonic!(a + b, c + d);
            }
            (false, false) => {}
        }
    }

    #[quickcheck]
    fn add_unordered_interval_associativity(
        a: UnorderedInterval,
        b: UnorderedInterval,
        c: UnorderedInterval,
    ) {
        assert_eq!((a + b) + c, a + (b + c));
    }

    #[quickcheck]
    fn add_unordered_interval_commutativity(a: UnorderedInterval, b: UnorderedInterval) {
        assert_eq!(a + b, b + a);
    }

    #[quickcheck]
    fn pitch_add_unordered_interval_compatibility(
        pitch: Pitch,
        interval_1: UnorderedInterval,
        interval_2: UnorderedInterval,
    ) {
        assert_eq!(
            (pitch + interval_1) + interval_2,
            pitch + (interval_1 + interval_2)
        );
    }

    #[quickcheck]
    fn unordered_interval_addunison(interval: UnorderedInterval) {
        assert_eq!(interval + UnorderedInterval::P1, interval);
    }

    #[quickcheck]
    fn unordered_interval_addoctave(interval: UnorderedInterval) {
        assert_eq!(
            interval + UnorderedInterval::P8,
            UnorderedInterval {
                octaves: interval.octaves + 1,
                ..interval
            }
        );
    }

    #[quickcheck]
    fn addand_sub_unordered_interval_are_inverses(a: UnorderedInterval, b: UnorderedInterval) {
        assert_eq!((a + b) - b, a);

        if let Ok(sub) = a.checked_sub(b) {
            assert_eq!(sub + b, a);
        }
    }

    #[quickcheck]
    fn sub_unordered_interval_err(a: UnorderedInterval, b: UnorderedInterval) {
        if a.interval_number() >= b.interval_number() {
            assert!(a.checked_sub(b).is_ok());
        } else {
            assert!(a.checked_sub(b).is_err());
        }
    }

    #[quickcheck]
    fn unordered_interval_sub_self(interval: UnorderedInterval) {
        assert_eq!(interval - interval, UnorderedInterval::P1);
    }

    #[test]
    fn add_ordered_interval_examples() {
        assert_eq!(
            UnorderedInterval::M3.ascending() + UnorderedInterval::m3.ascending(),
            UnorderedInterval::P5.ascending()
        );

        assert_eq!(
            UnorderedInterval::P5.ascending() + UnorderedInterval::P4.ascending(),
            UnorderedInterval::P8.ascending()
        );

        assert_eq!(
            UnorderedInterval::M9.descending() + UnorderedInterval::A6.descending(),
            UnorderedInterval::A14.descending()
        );

        assert_eq!(
            UnorderedInterval::M9.ascending() + UnorderedInterval::d3.descending(),
            UnorderedInterval::A7.ascending()
        );

        assert_eq!(
            UnorderedInterval::M2.ascending() + UnorderedInterval::d3.descending(),
            UnorderedInterval::d2.descending()
        );

        assert_eq!(
            UnorderedInterval::P4.descending() + UnorderedInterval::M2.ascending(),
            UnorderedInterval::m3.descending()
        );

        assert_eq!(
            UnorderedInterval::P8.descending() + UnorderedInterval::P15.ascending(),
            UnorderedInterval::P8.ascending()
        );
    }

    #[test]
    fn sub_ordered_interval_examples() {
        assert_eq!(
            UnorderedInterval::P5.ascending() - UnorderedInterval::m3.ascending(),
            UnorderedInterval::M3.ascending()
        );

        assert_eq!(
            UnorderedInterval::P1.ascending() - UnorderedInterval::A1.ascending(),
            UnorderedInterval::d1.ascending()
        );
    }

    #[quickcheck]
    fn add_ordered_interval_semitones_tet12(a: OrderedInterval, b: OrderedInterval) {
        assert_eq!(
            (a + b).semitones_tet12(),
            a.semitones_tet12() + b.semitones_tet12()
        );
    }

    #[quickcheck]
    fn sub_ordered_interval_semitones_tet12(a: OrderedInterval, b: OrderedInterval) {
        assert_eq!(
            (a - b).semitones_tet12(),
            a.semitones_tet12() - b.semitones_tet12()
        );
    }

    #[quickcheck]
    fn add_ordered_interval_preserves_enharmonic_equivalence(
        a: OrderedInterval,
        b: OrderedInterval,
        c: OrderedInterval,
        d: OrderedInterval,
    ) {
        match (a.enharmonic(&b), c.enharmonic(&d)) {
            (true, true) => {
                assert_enharmonic!(a + b, c + d);
            }
            (true, false) | (false, true) => {
                assert_not_enharmonic!(a + b, c + d);
            }
            (false, false) => {}
        }
    }

    #[quickcheck]
    fn add_ordered_interval_associativity(
        a: OrderedInterval,
        b: OrderedInterval,
        c: OrderedInterval,
    ) {
        assert_eq!((a + b) + c, a + (b + c));
    }

    #[quickcheck]
    fn add_ordered_interval_commutativity(a: OrderedInterval, b: OrderedInterval) {
        assert_eq!(a + b, b + a);
    }

    #[quickcheck]
    fn pitch_add_ordered_interval_compatibility(
        pitch: Pitch,
        interval_1: OrderedInterval,
        interval_2: OrderedInterval,
    ) {
        assert_eq!(
            (pitch + interval_1) + interval_2,
            pitch + (interval_1 + interval_2)
        );
    }

    #[quickcheck]
    fn addand_sub_ordered_interval_are_inverses(a: OrderedInterval, b: OrderedInterval) {
        assert_eq!((a + b) - b, a);
        assert_eq!((a - b) + b, a);
    }

    #[quickcheck]
    fn addand_sub_ordered_interval_ascending_descending(a: OrderedInterval, b: UnorderedInterval) {
        assert_eq!(a + b.ascending(), a - b.descending());
        assert_eq!(a + b.descending(), a - b.ascending());
    }

    #[quickcheck]
    fn add_ordered_interval_neg_distributes(a: OrderedInterval, b: OrderedInterval) {
        assert_eq!(-(a + b), (-a) + (-b));
    }

    #[quickcheck]
    fn unordered_simple_interval_invert(interval: UnorderedSimpleInterval) {
        assert_eq!(
            interval.wrapping_add(interval.invert()),
            UnorderedSimpleInterval::P1
        );

        assert_eq!(
            interval.invert(),
            UnorderedSimpleInterval::P1.wrapping_sub(interval)
        );
    }

    #[quickcheck]
    fn unordered_simple_interval_invert_interval_number(interval: UnorderedSimpleInterval) {
        assert_eq!(
            interval.invert().interval_number(),
            interval.interval_number().invert()
        );
    }

    #[quickcheck]
    fn unordered_interval_mul_usize(interval: UnorderedInterval, times: usize) {
        let times = times % 100;

        let mut expected_output = UnorderedInterval::P1;
        for _ in 0..times {
            expected_output += interval;
        }

        assert_eq!(interval * times, expected_output);
    }

    #[quickcheck]
    fn ordered_interval_mul_isize(interval: OrderedInterval, times: isize) {
        let times = times % 100;

        let mut expected_output = UnorderedInterval::P1.ascending();
        if times >= 0 {
            for _ in 0..times {
                expected_output += interval;
            }
        } else {
            for _ in 0..-times {
                expected_output -= interval;
            }
        }

        assert_eq!(interval * times, expected_output);
    }
}
