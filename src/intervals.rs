use std::{
    fmt::Display,
    num::NonZeroUsize,
    ops::{Add, Neg, Sub},
};

use num2words::Num2Words;
use paste::paste;

use crate::{
    enharmonic::Enharmonic,
    pitches::{Accidental, Letter, Pitch, PitchClass},
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

impl Add<UnorderedSimpleIntervalNumber> for Letter {
    type Output = Self;

    fn add(self, rhs: UnorderedSimpleIntervalNumber) -> Self::Output {
        Self::try_from_index_within_octave(
            (self.index_within_octave() + rhs.zero_based()).rem_euclid(7),
        )
        .expect("index should be in valid range")
    }
}

impl Sub<UnorderedSimpleIntervalNumber> for Letter {
    type Output = Self;

    fn sub(self, rhs: UnorderedSimpleIntervalNumber) -> Self::Output {
        Self::try_from_index_within_octave(
            (self.index_within_octave() as isize - rhs.zero_based() as isize).rem_euclid(7)
                as usize,
        )
        .expect("index should be in valid range")
    }
}

impl Sub for UnorderedSimpleIntervalNumber {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.checked_sub(rhs)
            .expect("attempted to subtract larger interval number from smaller interval number")
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
    (Perfect, $number:ident) => {
        paste! {
            pub const [< DOUBLY_AUGMENTED_$number:upper >]: Self =
                Self::$number(PerfectIntervalQuality::Augmented(NonZeroUsize::new(2).unwrap()));
            pub const [< AUGMENTED_$number:upper >]: Self =
                Self::$number(PerfectIntervalQuality::Augmented(NonZeroUsize::new(1).unwrap()));
            pub const [< PERFECT_$number:upper >]: Self =
                Self::$number(PerfectIntervalQuality::Perfect);
            pub const [< DIMINISHED_$number:upper >]: Self =
                Self::$number(PerfectIntervalQuality::Diminished(NonZeroUsize::new(1).unwrap()));
            pub const [< DOUBLY_DIMINISHED_$number:upper >]: Self =
                Self::$number(PerfectIntervalQuality::Diminished(NonZeroUsize::new(2).unwrap()));
        }
    };
    (MajorMinor, $number:ident) => {
        paste! {
            pub const [< DOUBLY_AUGMENTED_$number:upper >]: Self =
                Self::$number(MajorMinorIntervalQuality::Augmented(NonZeroUsize::new(2).unwrap()));
            pub const [< AUGMENTED_$number:upper >]: Self =
                Self::$number(MajorMinorIntervalQuality::Augmented(NonZeroUsize::new(1).unwrap()));
            pub const [< MAJOR_$number:upper >]: Self =
                Self::$number(MajorMinorIntervalQuality::Major);
            pub const [< MINOR_$number:upper >]: Self =
                Self::$number(MajorMinorIntervalQuality::Minor);
            pub const [< DIMINISHED_$number:upper >]: Self =
                Self::$number(MajorMinorIntervalQuality::Diminished(NonZeroUsize::new(1).unwrap()));
            pub const [< DOUBLY_DIMINISHED_$number:upper >]: Self =
                Self::$number(MajorMinorIntervalQuality::Diminished(NonZeroUsize::new(2).unwrap()));
        }
    };
}

impl UnorderedSimpleInterval {
    #[doc(alias = "HALF_STEP")]
    pub const SEMITONE: Self = Self::MINOR_SECOND;

    #[doc(alias = "WHOLE_TONE")]
    #[doc(alias = "STEP")]
    #[doc(alias = "WHOLE_STEP")]
    pub const TONE: Self = Self::MAJOR_SECOND;

    make_unordered_simple_interval_consts!(Perfect, Unison);
    make_unordered_simple_interval_consts!(MajorMinor, Second);
    make_unordered_simple_interval_consts!(MajorMinor, Third);
    make_unordered_simple_interval_consts!(Perfect, Fourth);
    make_unordered_simple_interval_consts!(Perfect, Fifth);
    make_unordered_simple_interval_consts!(MajorMinor, Sixth);
    make_unordered_simple_interval_consts!(MajorMinor, Seventh);

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
        let interval_number = self.interval_number().checked_sub(rhs.interval_number())?;

        let semitones_tet12 = self.semitones_tet12() - rhs.semitones_tet12();

        Ok(match interval_number {
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
        })
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

impl Add<UnorderedSimpleInterval> for PitchClass {
    type Output = Self;

    fn add(self, rhs: UnorderedSimpleInterval) -> Self::Output {
        let letter = self.letter + rhs.interval_number();

        let goes_into_next_octave = letter < self.letter;

        let accidental = Accidental::from_semitones_tet12(
            self.semitones_within_octave_tet12_non_wrapping() as isize + rhs.semitones_tet12()
                - (letter.semitones_within_octave_tet12() as isize
                    + if goes_into_next_octave { 12 } else { 0 }),
        );

        Self { letter, accidental }
    }
}

impl Sub<UnorderedSimpleInterval> for PitchClass {
    type Output = Self;

    fn sub(self, rhs: UnorderedSimpleInterval) -> Self::Output {
        let letter = self.letter - rhs.interval_number();

        let goes_into_previous_octave = letter > self.letter;

        let accidental = Accidental::from_semitones_tet12(
            self.semitones_within_octave_tet12_non_wrapping() as isize
                - rhs.semitones_tet12()
                - (letter.semitones_within_octave_tet12() as isize
                    - if goes_into_previous_octave { 12 } else { 0 }),
        );

        Self { letter, accidental }
    }
}

impl Add<UnorderedSimpleInterval> for Pitch {
    type Output = Self;

    fn add(self, rhs: UnorderedSimpleInterval) -> Self::Output {
        let Self { octave, class } = self;

        let octave = octave
            + (class.letter.index_within_octave() + rhs.interval_number().zero_based())
                .div_euclid(7) as isize;

        let class = self.class + rhs;

        Self { octave, class }
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

        let class = self.class - rhs;

        Self { octave, class }
    }
}

impl Sub for UnorderedSimpleInterval {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.checked_sub(rhs)
            .expect("attempted to subtract larger interval from smaller interval")
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

impl Sub for UnorderedIntervalNumber {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.checked_sub(rhs)
            .expect("attempted to subtract larger interval from smaller interval")
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UnorderedInterval {
    pub octaves: usize,
    pub simple: UnorderedSimpleInterval,
}

macro_rules! make_unordered_interval_consts {
    (Perfect, $ident:ident, $simple:ident, $octaves:literal) => {
        paste! {
            pub const [< DOUBLY_AUGMENTED_$ident:upper >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimpleInterval::[< DOUBLY_AUGMENTED_$simple:upper >],
            };
            pub const [< AUGMENTED_$ident:upper >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimpleInterval::[< AUGMENTED_$simple:upper >],
            };
            pub const [< PERFECT_$ident:upper >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimpleInterval::[< PERFECT_$simple:upper >],
            };
            pub const [< DIMINISHED_$ident:upper >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimpleInterval::[< DIMINISHED_$simple:upper >],
            };
            pub const [< DOUBLY_DIMINISHED_$ident:upper >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimpleInterval::[< DOUBLY_DIMINISHED_$simple:upper >],
            };
        }
    };
    (MajorMinor, $ident:ident, $simple:ident, $octaves:literal) => {
        paste! {
            pub const [< DOUBLY_AUGMENTED_$ident:upper >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimpleInterval::[< DOUBLY_AUGMENTED_$simple:upper >],
            };
            pub const [< AUGMENTED_$ident:upper >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimpleInterval::[< AUGMENTED_$simple:upper >],
            };
            pub const [< MAJOR_$ident:upper >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimpleInterval::[< MAJOR_$simple:upper >],
            };
            pub const [< MINOR_$ident:upper >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimpleInterval::[< MINOR_$simple:upper >],
            };
            pub const [< DIMINISHED_$ident:upper >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimpleInterval::[< DIMINISHED_$simple:upper >],
            };
            pub const [< DOUBLY_DIMINISHED_$ident:upper >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimpleInterval::[< DOUBLY_DIMINISHED_$simple:upper >],
            };
        }
    };
}

impl UnorderedInterval {
    #[doc(alias = "HALF_STEP")]
    pub const SEMITONE: Self = Self {
        octaves: 0,
        simple: UnorderedSimpleInterval::SEMITONE,
    };

    #[doc(alias = "WHOLE_TONE")]
    #[doc(alias = "STEP")]
    #[doc(alias = "WHOLE_STEP")]
    pub const TONE: Self = Self {
        octaves: 0,
        simple: UnorderedSimpleInterval::TONE,
    };

    make_unordered_interval_consts!(Perfect, UNISON, Unison, 0);
    make_unordered_interval_consts!(MajorMinor, SECOND, Second, 0);
    make_unordered_interval_consts!(MajorMinor, THIRD, Third, 0);
    make_unordered_interval_consts!(Perfect, FOURTH, Fourth, 0);
    make_unordered_interval_consts!(Perfect, FIFTH, Fifth, 0);
    make_unordered_interval_consts!(MajorMinor, SIXTH, Sixth, 0);
    make_unordered_interval_consts!(MajorMinor, SEVENTH, Seventh, 0);

    pub const DOUBLY_DIMINISHED_OCTAVE: Self = Self {
        octaves: 1,
        simple: UnorderedSimpleInterval::DOUBLY_DIMINISHED_UNISON,
    };

    pub const DIMINISHED_OCTAVE: Self = Self {
        octaves: 1,
        simple: UnorderedSimpleInterval::DIMINISHED_UNISON,
    };

    #[doc(alias = "OCTAVE")]
    pub const PERFECT_OCTAVE: Self = Self {
        octaves: 1,
        simple: UnorderedSimpleInterval::PERFECT_UNISON,
    };

    pub const AUGMENTED_OCTAVE: Self = Self {
        octaves: 1,
        simple: UnorderedSimpleInterval::AUGMENTED_UNISON,
    };

    pub const DOUBLY_AUGMENTED_OCTAVE: Self = Self {
        octaves: 1,
        simple: UnorderedSimpleInterval::DOUBLY_AUGMENTED_UNISON,
    };

    make_unordered_interval_consts!(MajorMinor, NINTH, Second, 1);
    make_unordered_interval_consts!(MajorMinor, TENTH, Third, 1);
    make_unordered_interval_consts!(Perfect, ELEVENTH, Fourth, 1);
    make_unordered_interval_consts!(Perfect, TWELFTH, Fifth, 1);
    make_unordered_interval_consts!(MajorMinor, THIRTEENTH, Sixth, 1);
    make_unordered_interval_consts!(MajorMinor, FOURTEENTH, Seventh, 1);

    #[doc(alias = "DOUBLE_OCTAVE")]
    pub const PERFECT_DOUBLE_OCTAVE: Self = Self {
        octaves: 2,
        simple: UnorderedSimpleInterval::PERFECT_UNISON,
    };

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

impl Add for UnorderedInterval {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let simple = self.simple.wrapping_add(rhs.simple);

        let goes_into_next_octave = simple.interval_number() < self.simple.interval_number();

        let octaves = self.octaves + rhs.octaves + if goes_into_next_octave { 1 } else { 0 };

        Self { octaves, simple }
    }
}

impl Sub for UnorderedInterval {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.checked_sub(rhs)
            .expect("attempted to subtract larger interval from smaller interval")
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntervalDirection {
    Descending,
    Ascending,
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
                unordered: UnorderedInterval::PERFECT_UNISON,
            } => UnorderedInterval::PERFECT_UNISON.fmt(f),
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
            UnorderedInterval::PERFECT_UNISON.ascending(),
            UnorderedInterval::PERFECT_UNISON.ascending()
        );
        assert_eq!(
            UnorderedInterval::PERFECT_UNISON.ascending(),
            UnorderedInterval::PERFECT_UNISON.descending()
        );
        assert_eq!(
            UnorderedInterval::PERFECT_UNISON.descending(),
            UnorderedInterval::PERFECT_UNISON.ascending()
        );
        assert_eq!(
            UnorderedInterval::PERFECT_UNISON.descending(),
            UnorderedInterval::PERFECT_UNISON.descending()
        );

        assert_eq!(
            UnorderedInterval::AUGMENTED_UNISON.ascending(),
            UnorderedInterval::DIMINISHED_UNISON.descending()
        );
        assert_eq!(
            UnorderedInterval::AUGMENTED_UNISON.descending(),
            UnorderedInterval::DIMINISHED_UNISON.ascending()
        );
        assert_ne!(
            UnorderedInterval::AUGMENTED_UNISON.ascending(),
            UnorderedInterval::DIMINISHED_UNISON.ascending()
        );
        assert_ne!(
            UnorderedInterval::AUGMENTED_UNISON.descending(),
            UnorderedInterval::DIMINISHED_UNISON.descending()
        );
    }

    #[test]
    fn ordered_interval_ordering_examples() {
        assert_eq!(
            UnorderedInterval::PERFECT_UNISON
                .ascending()
                .cmp(&UnorderedInterval::PERFECT_UNISON.ascending()),
            std::cmp::Ordering::Equal,
        );
        assert_eq!(
            UnorderedInterval::DIMINISHED_UNISON
                .ascending()
                .cmp(&UnorderedInterval::PERFECT_UNISON.ascending()),
            std::cmp::Ordering::Less,
        );
        assert_eq!(
            UnorderedInterval::DIMINISHED_UNISON
                .ascending()
                .cmp(&UnorderedInterval::AUGMENTED_UNISON.ascending()),
            std::cmp::Ordering::Less,
        );
        assert_eq!(
            UnorderedInterval::DIMINISHED_UNISON
                .descending()
                .cmp(&UnorderedInterval::AUGMENTED_UNISON.ascending()),
            std::cmp::Ordering::Equal,
        );
        assert_eq!(
            UnorderedInterval::DIMINISHED_UNISON
                .descending()
                .cmp(&UnorderedInterval::AUGMENTED_UNISON.descending()),
            std::cmp::Ordering::Greater,
        );

        assert_eq!(
            UnorderedInterval::MAJOR_SECOND
                .descending()
                .cmp(&UnorderedInterval::PERFECT_UNISON.ascending()),
            std::cmp::Ordering::Less,
        );
        assert_eq!(
            UnorderedInterval::MAJOR_SECOND
                .descending()
                .cmp(&UnorderedInterval::MAJOR_SECOND.ascending()),
            std::cmp::Ordering::Less,
        );

        assert_eq!(
            UnorderedInterval::MAJOR_SECOND
                .ascending()
                .cmp(&UnorderedInterval::MINOR_THIRD.ascending()),
            std::cmp::Ordering::Less,
        );
        assert_eq!(
            UnorderedInterval::AUGMENTED_FIFTH
                .ascending()
                .cmp(&UnorderedInterval::MINOR_SIXTH.ascending()),
            std::cmp::Ordering::Less,
        );
        assert_eq!(
            UnorderedInterval::AUGMENTED_FIFTH
                .ascending()
                .cmp(&UnorderedInterval::DIMINISHED_SIXTH.ascending()),
            std::cmp::Ordering::Less,
        );

        assert_eq!(
            UnorderedInterval::MAJOR_THIRD
                .descending()
                .cmp(&UnorderedInterval::PERFECT_FIFTH.descending()),
            std::cmp::Ordering::Greater,
        );
        assert_eq!(
            UnorderedInterval::MAJOR_THIRD
                .descending()
                .cmp(&UnorderedInterval::DOUBLY_AUGMENTED_FOURTH.descending()),
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
        assert_eq!(
            format!("{}", UnorderedInterval::PERFECT_UNISON.ascending()),
            "P1"
        );

        assert_eq!(
            format!("{}", UnorderedInterval::MAJOR_NINTH.ascending()),
            "+M9"
        );

        assert_eq!(
            format!("{}", UnorderedInterval::MINOR_SEVENTH.descending()),
            "-m7"
        );

        assert_eq!(
            format!("{}", UnorderedInterval::AUGMENTED_FIFTH.descending()),
            "-A5"
        );

        assert_eq!(
            format!(
                "{}",
                UnorderedInterval::DOUBLY_DIMINISHED_ELEVENTH.ascending()
            ),
            "+dd11"
        );

        assert_eq!(
            format!("{:#}", UnorderedInterval::AUGMENTED_UNISON.ascending()),
            "ascending augmented unison"
        );

        assert_eq!(
            format!("{:#}", UnorderedInterval::PERFECT_OCTAVE.ascending()),
            "ascending perfect octave"
        );

        assert_eq!(
            format!("{:#}", UnorderedInterval::AUGMENTED_OCTAVE.ascending()),
            "ascending augmented octave"
        );

        assert_eq!(
            format!(
                "{:#}",
                UnorderedInterval::PERFECT_DOUBLE_OCTAVE.descending()
            ),
            "descending perfect double octave"
        );

        assert_eq!(
            format!(
                "{:#}",
                UnorderedInterval {
                    octaves: 3,
                    simple: UnorderedSimpleInterval::DIMINISHED_UNISON
                }
                .ascending()
            ),
            "ascending diminished 3x octave"
        );

        assert_eq!(
            format!("{:#}", UnorderedInterval::MAJOR_THIRD.descending()),
            "descending major third"
        );

        assert_eq!(
            format!("{:#}", UnorderedInterval::MINOR_NINTH.descending()),
            "descending minor ninth"
        );

        assert_eq!(
            format!(
                "{:#}",
                UnorderedInterval::DOUBLY_AUGMENTED_FIFTH.ascending()
            ),
            "ascending doubly augmented fifth"
        );

        assert_eq!(
            format!(
                "{:#}",
                UnorderedInterval::DOUBLY_DIMINISHED_SECOND
                    .diminish()
                    .diminish()
                    .descending()
            ),
            "descending 4x diminished second"
        );
    }

    #[quickcheck]
    fn ordered_interval_enharmonic_examples() {
        assert_enharmonic!(
            UnorderedInterval::PERFECT_UNISON.ascending(),
            UnorderedInterval::PERFECT_UNISON.ascending()
        );

        assert_enharmonic!(
            UnorderedInterval::AUGMENTED_THIRD.ascending(),
            UnorderedInterval::PERFECT_FOURTH.ascending()
        );

        assert_enharmonic!(
            UnorderedInterval::DOUBLY_DIMINISHED_SECOND.ascending(),
            UnorderedInterval::MINOR_SECOND.descending()
        );

        assert_enharmonic!(
            UnorderedInterval::AUGMENTED_FOURTH.descending(),
            UnorderedInterval::DIMINISHED_FIFTH.descending()
        );

        assert_enharmonic!(
            UnorderedInterval::DOUBLY_AUGMENTED_SEVENTH.ascending(),
            UnorderedInterval::AUGMENTED_OCTAVE.ascending()
        );

        assert_not_enharmonic!(
            UnorderedInterval::PERFECT_UNISON.ascending(),
            UnorderedInterval::PERFECT_OCTAVE.ascending()
        );

        assert_not_enharmonic!(
            UnorderedInterval::MAJOR_THIRD.ascending(),
            UnorderedInterval::MAJOR_THIRD.descending()
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
        assert_eq!(
            Pitch::C4 + UnorderedInterval::MAJOR_THIRD.ascending(),
            Pitch::E4
        );

        assert_eq!(
            Pitch::C4 + UnorderedInterval::MINOR_SECOND.ascending(),
            Pitch::Db4
        );

        assert_eq!(
            Pitch::E4 + UnorderedInterval::MINOR_SECOND.ascending(),
            Pitch::F4
        );

        assert_eq!(
            Pitch::A4 + UnorderedInterval::MINOR_THIRD.ascending(),
            Pitch::C5
        );

        assert_eq!(
            Pitch::G2 + UnorderedInterval::AUGMENTED_TWELFTH.ascending(),
            Pitch::Ds4
        );

        assert_eq!(
            Pitch::C3 + UnorderedInterval::MAJOR_SECOND.descending(),
            Pitch::Bb2
        );

        assert_eq!(
            Pitch::E6 + UnorderedInterval::MAJOR_THIRD.descending(),
            Pitch::C6
        );

        assert_eq!(
            Pitch::Fb3 + UnorderedInterval::DOUBLY_DIMINISHED_NINTH.descending(),
            Pitch::Es2
        );
    }

    #[quickcheck]
    fn pitch_add_ordered_interval_equals_sub_neg(pitch: Pitch, interval: OrderedInterval) {
        assert_eq!(pitch + interval, pitch - (-interval));
    }

    #[quickcheck]
    fn pitch_sub_ordered_interval_equals_add_neg(pitch: Pitch, interval: OrderedInterval) {
        assert_eq!(pitch - interval, pitch + (-interval));
    }

    #[quickcheck]
    fn pitch_add_and_sub_ordered_interval_are_inverses(pitch: Pitch, interval: OrderedInterval) {
        assert_eq!((pitch + interval) - interval, pitch);
        assert_eq!((pitch - interval) + interval, pitch);
    }

    #[quickcheck]
    fn pitch_add_unison(pitch: Pitch) {
        assert_eq!(pitch + UnorderedInterval::PERFECT_UNISON, pitch);
        assert_eq!(pitch + UnorderedInterval::PERFECT_UNISON.ascending(), pitch);
        assert_eq!(
            pitch + UnorderedInterval::PERFECT_UNISON.descending(),
            pitch
        );
    }

    #[quickcheck]
    fn pitch_sub_unison(pitch: Pitch) {
        assert_eq!(pitch - UnorderedInterval::PERFECT_UNISON, pitch);
        assert_eq!(pitch - UnorderedInterval::PERFECT_UNISON.ascending(), pitch);
        assert_eq!(
            pitch - UnorderedInterval::PERFECT_UNISON.descending(),
            pitch
        );
    }

    #[quickcheck]
    fn pitch_add_octave(pitch: Pitch) {
        assert_eq!(pitch + UnorderedInterval::PERFECT_OCTAVE, pitch.octave_up());
    }

    #[quickcheck]
    fn pitch_sub_octave(pitch: Pitch) {
        assert_eq!(
            pitch - UnorderedInterval::PERFECT_OCTAVE,
            pitch.octave_down()
        );
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
            UnorderedInterval::MAJOR_THIRD + UnorderedInterval::MINOR_THIRD,
            UnorderedInterval::PERFECT_FIFTH
        );

        assert_eq!(
            UnorderedInterval::PERFECT_FIFTH + UnorderedInterval::PERFECT_FOURTH,
            UnorderedInterval::PERFECT_OCTAVE
        );

        assert_eq!(
            UnorderedInterval::DIMINISHED_SIXTH + UnorderedInterval::DOUBLY_AUGMENTED_FIFTH,
            UnorderedInterval::MAJOR_TENTH
        );
    }

    #[test]
    fn sub_unordered_interval_examples() {
        assert_eq!(
            UnorderedInterval::PERFECT_FIFTH - UnorderedInterval::MINOR_THIRD,
            UnorderedInterval::MAJOR_THIRD
        );

        assert_eq!(
            UnorderedInterval::PERFECT_UNISON - UnorderedInterval::AUGMENTED_UNISON,
            UnorderedInterval::DIMINISHED_UNISON
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
    fn unordered_interval_add_unison(interval: UnorderedInterval) {
        assert_eq!(interval + UnorderedInterval::PERFECT_UNISON, interval);
    }

    #[quickcheck]
    fn unordered_interval_add_octave(interval: UnorderedInterval) {
        assert_eq!(
            interval + UnorderedInterval::PERFECT_OCTAVE,
            UnorderedInterval {
                octaves: interval.octaves + 1,
                ..interval
            }
        );
    }

    #[quickcheck]
    fn add_and_sub_unordered_interval_are_inverses(a: UnorderedInterval, b: UnorderedInterval) {
        assert_eq!((a + b) - b, a);

        if let Ok(sub) = a.checked_sub(b) {
            assert_eq!(sub + b, a);
        }
    }

    #[quickcheck]
    fn sub_unordered_interval_err(a: UnorderedInterval, b: UnorderedInterval) {
        if a >= b {
            assert!(a.checked_sub(b).is_ok());
        } else {
            assert!(a.checked_sub(b).is_err());
        }
    }

    #[quickcheck]
    fn unordered_interval_sub_self(interval: UnorderedInterval) {
        assert_eq!(interval - interval, UnorderedInterval::PERFECT_UNISON);
    }
}
