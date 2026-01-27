use std::{fmt::Display, num::NonZeroUsize, ops::Neg};

use num2words::Num2Words;
use paste::paste;

use crate::{enharmonic::Enharmonic, tuning::TET12};

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
pub enum OrderedPitchClassIntervalNumber {
    Unison,
    Second,
    Third,
    Fourth,
    Fifth,
    Sixth,
    Seventh,
    Octave,
}

impl OrderedPitchClassIntervalNumber {
    pub fn zero_based(&self) -> usize {
        match self {
            Self::Unison => 0,
            Self::Second => 1,
            Self::Third => 2,
            Self::Fourth => 3,
            Self::Fifth => 4,
            Self::Sixth => 5,
            Self::Seventh => 6,
            Self::Octave => 7,
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
            7 => Ok(Self::Octave),
            _ => Err(()),
        }
    }

    pub fn try_from_one_based(number: usize) -> Result<Self, ()> {
        match number {
            0 => Err(()),
            _ => Self::try_from_zero_based(number - 1),
        }
    }
}

impl Display for OrderedPitchClassIntervalNumber {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            match self {
                Self::Unison => write!(f, "unison"),
                Self::Octave => write!(f, "octave"),
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OrderedPitchClassInterval {
    AugmentedUnison(usize),
    Second(MajorMinorIntervalQuality),
    Third(MajorMinorIntervalQuality),
    Fourth(PerfectIntervalQuality),
    Fifth(PerfectIntervalQuality),
    Sixth(MajorMinorIntervalQuality),
    Seventh(MajorMinorIntervalQuality),
    DiminishedOctave(NonZeroUsize),
}

macro_rules! make_ordered_pitch_class_interval_consts {
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

impl OrderedPitchClassInterval {
    #[doc(alias = "HALF_STEP")]
    pub const SEMITONE: Self = Self::MINOR_SECOND;

    #[doc(alias = "WHOLE_TONE")]
    #[doc(alias = "STEP")]
    #[doc(alias = "WHOLE_STEP")]
    pub const TONE: Self = Self::MAJOR_SECOND;

    pub const PERFECT_UNISON: Self = Self::AugmentedUnison(0);
    pub const AUGMENTED_UNISON: Self = Self::AugmentedUnison(1);
    pub const DOUBLY_AUGMENTED_UNISON: Self = Self::AugmentedUnison(2);

    make_ordered_pitch_class_interval_consts!(MajorMinor, Second);
    make_ordered_pitch_class_interval_consts!(MajorMinor, Third);
    make_ordered_pitch_class_interval_consts!(Perfect, Fourth);
    make_ordered_pitch_class_interval_consts!(Perfect, Fifth);
    make_ordered_pitch_class_interval_consts!(MajorMinor, Sixth);
    make_ordered_pitch_class_interval_consts!(MajorMinor, Seventh);

    pub const DIMINISHED_OCTAVE: Self = Self::DiminishedOctave(NonZeroUsize::new(1).unwrap());
    pub const DOUBLY_DIMINISHED_OCTAVE: Self =
        Self::DiminishedOctave(NonZeroUsize::new(2).unwrap());

    pub const fn interval_number(&self) -> OrderedPitchClassIntervalNumber {
        match self {
            Self::AugmentedUnison(_) => OrderedPitchClassIntervalNumber::Unison,
            Self::Second(_) => OrderedPitchClassIntervalNumber::Second,
            Self::Third(_) => OrderedPitchClassIntervalNumber::Third,
            Self::Fourth(_) => OrderedPitchClassIntervalNumber::Fourth,
            Self::Fifth(_) => OrderedPitchClassIntervalNumber::Fifth,
            Self::Sixth(_) => OrderedPitchClassIntervalNumber::Sixth,
            Self::Seventh(_) => OrderedPitchClassIntervalNumber::Seventh,
            Self::DiminishedOctave(_) => OrderedPitchClassIntervalNumber::Octave,
        }
    }

    pub fn quality(&self) -> IntervalQuality {
        match self {
            Self::AugmentedUnison(times) => NonZeroUsize::new(*times)
                .map(IntervalQuality::Augmented)
                .unwrap_or(IntervalQuality::Perfect),
            Self::Second(quality)
            | Self::Third(quality)
            | Self::Sixth(quality)
            | Self::Seventh(quality) => (*quality).into(),
            Self::Fourth(quality) | Self::Fifth(quality) => (*quality).into(),
            Self::DiminishedOctave(times) => IntervalQuality::Diminished(*times),
        }
    }
}

impl PartialOrd for OrderedPitchClassInterval {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OrderedPitchClassInterval {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        fn index(interval: &OrderedPitchClassInterval) -> impl Ord {
            (
                interval.interval_number(),
                match interval {
                    OrderedPitchClassInterval::AugmentedUnison(times) => *times as isize,
                    OrderedPitchClassInterval::Second(quality) => quality.index(),
                    OrderedPitchClassInterval::Third(quality) => quality.index(),
                    OrderedPitchClassInterval::Fourth(quality) => quality.index(),
                    OrderedPitchClassInterval::Fifth(quality) => quality.index(),
                    OrderedPitchClassInterval::Sixth(quality) => quality.index(),
                    OrderedPitchClassInterval::Seventh(quality) => quality.index(),
                    OrderedPitchClassInterval::DiminishedOctave(times) => -(times.get() as isize),
                },
            )
        }

        index(self).cmp(&index(other))
    }
}

impl Enharmonic for OrderedPitchClassInterval {
    fn enharmonic(&self, other: &Self) -> bool {
        TET12::semitones(self) == TET12::semitones(other)
    }
}

impl Display for OrderedPitchClassInterval {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.quality().fmt(f)?;

        if f.alternate() {
            " ".fmt(f)?;
        }

        self.interval_number().fmt(f)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UnorderedSimplePitchIntervalNumber {
    Unison,
    Second,
    Third,
    Fourth,
    Fifth,
    Sixth,
    Seventh,
}

impl UnorderedSimplePitchIntervalNumber {
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
}

impl Display for UnorderedSimplePitchIntervalNumber {
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
pub enum UnorderedSimplePitchInterval {
    Unison(PerfectIntervalQuality),
    Second(MajorMinorIntervalQuality),
    Third(MajorMinorIntervalQuality),
    Fourth(PerfectIntervalQuality),
    Fifth(PerfectIntervalQuality),
    Sixth(MajorMinorIntervalQuality),
    Seventh(MajorMinorIntervalQuality),
}

macro_rules! make_unordered_simple_pitch_interval_consts {
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

impl UnorderedSimplePitchInterval {
    #[doc(alias = "HALF_STEP")]
    pub const SEMITONE: Self = Self::MINOR_SECOND;

    #[doc(alias = "WHOLE_TONE")]
    #[doc(alias = "STEP")]
    #[doc(alias = "WHOLE_STEP")]
    pub const TONE: Self = Self::MAJOR_SECOND;

    make_unordered_simple_pitch_interval_consts!(Perfect, Unison);
    make_unordered_simple_pitch_interval_consts!(MajorMinor, Second);
    make_unordered_simple_pitch_interval_consts!(MajorMinor, Third);
    make_unordered_simple_pitch_interval_consts!(Perfect, Fourth);
    make_unordered_simple_pitch_interval_consts!(Perfect, Fifth);
    make_unordered_simple_pitch_interval_consts!(MajorMinor, Sixth);
    make_unordered_simple_pitch_interval_consts!(MajorMinor, Seventh);

    pub const fn interval_number(&self) -> UnorderedSimplePitchIntervalNumber {
        match self {
            Self::Unison(_) => UnorderedSimplePitchIntervalNumber::Unison,
            Self::Second(_) => UnorderedSimplePitchIntervalNumber::Second,
            Self::Third(_) => UnorderedSimplePitchIntervalNumber::Third,
            Self::Fourth(_) => UnorderedSimplePitchIntervalNumber::Fourth,
            Self::Fifth(_) => UnorderedSimplePitchIntervalNumber::Fifth,
            Self::Sixth(_) => UnorderedSimplePitchIntervalNumber::Sixth,
            Self::Seventh(_) => UnorderedSimplePitchIntervalNumber::Seventh,
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
}

impl Enharmonic for UnorderedSimplePitchInterval {
    fn enharmonic(&self, other: &Self) -> bool {
        TET12::semitones(self) == TET12::semitones(other)
    }
}

impl Display for UnorderedSimplePitchInterval {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.quality().fmt(f)?;

        if f.alternate() {
            " ".fmt(f)?;
        }

        self.interval_number().fmt(f)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UnorderedPitchIntervalNumber {
    pub octaves: usize,
    pub simple: UnorderedSimplePitchIntervalNumber,
}

impl UnorderedPitchIntervalNumber {
    pub const UNISON: Self = Self {
        octaves: 0,
        simple: UnorderedSimplePitchIntervalNumber::Unison,
    };

    pub const SECOND: Self = Self {
        octaves: 0,
        simple: UnorderedSimplePitchIntervalNumber::Second,
    };

    pub const THIRD: Self = Self {
        octaves: 0,
        simple: UnorderedSimplePitchIntervalNumber::Third,
    };

    pub const FOURTH: Self = Self {
        octaves: 0,
        simple: UnorderedSimplePitchIntervalNumber::Fourth,
    };

    pub const FIFTH: Self = Self {
        octaves: 0,
        simple: UnorderedSimplePitchIntervalNumber::Fifth,
    };

    pub const SIXTH: Self = Self {
        octaves: 0,
        simple: UnorderedSimplePitchIntervalNumber::Sixth,
    };

    pub const SEVENTH: Self = Self {
        octaves: 0,
        simple: UnorderedSimplePitchIntervalNumber::Seventh,
    };

    pub const OCTAVE: Self = Self {
        octaves: 1,
        simple: UnorderedSimplePitchIntervalNumber::Unison,
    };

    pub const NINTH: Self = Self {
        octaves: 1,
        simple: UnorderedSimplePitchIntervalNumber::Second,
    };

    pub const TENTH: Self = Self {
        octaves: 1,
        simple: UnorderedSimplePitchIntervalNumber::Third,
    };

    pub const ELEVENTH: Self = Self {
        octaves: 1,
        simple: UnorderedSimplePitchIntervalNumber::Fourth,
    };

    pub const TWELFTH: Self = Self {
        octaves: 1,
        simple: UnorderedSimplePitchIntervalNumber::Fifth,
    };

    pub const THIRTEENTH: Self = Self {
        octaves: 1,
        simple: UnorderedSimplePitchIntervalNumber::Sixth,
    };

    pub const FOURTEENTH: Self = Self {
        octaves: 1,
        simple: UnorderedSimplePitchIntervalNumber::Seventh,
    };

    pub const DOUBLE_OCTAVE: Self = Self {
        octaves: 2,
        simple: UnorderedSimplePitchIntervalNumber::Unison,
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
            simple: UnorderedSimplePitchIntervalNumber::try_from_zero_based(number % 7)
                .expect("number should be in valid range"),
        }
    }

    pub fn try_from_one_based(number: usize) -> Result<Self, ()> {
        match number {
            0 => Err(()),
            _ => Ok(Self::from_zero_based(number - 1)),
        }
    }
}

impl From<UnorderedSimplePitchIntervalNumber> for UnorderedPitchIntervalNumber {
    fn from(simple: UnorderedSimplePitchIntervalNumber) -> Self {
        Self { octaves: 0, simple }
    }
}

impl Display for UnorderedPitchIntervalNumber {
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UnorderedPitchInterval {
    pub octaves: usize,
    pub simple: UnorderedSimplePitchInterval,
}

macro_rules! make_unordered_pitch_interval_consts {
    (Perfect, $ident:ident, $simple:ident, $octaves:literal) => {
        paste! {
            pub const [< DOUBLY_AUGMENTED_$ident:upper >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimplePitchInterval::[< DOUBLY_AUGMENTED_$simple:upper >],
            };
            pub const [< AUGMENTED_$ident:upper >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimplePitchInterval::[< AUGMENTED_$simple:upper >],
            };
            pub const [< PERFECT_$ident:upper >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimplePitchInterval::[< PERFECT_$simple:upper >],
            };
            pub const [< DIMINISHED_$ident:upper >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimplePitchInterval::[< DIMINISHED_$simple:upper >],
            };
            pub const [< DOUBLY_DIMINISHED_$ident:upper >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimplePitchInterval::[< DOUBLY_DIMINISHED_$simple:upper >],
            };
        }
    };
    (MajorMinor, $ident:ident, $simple:ident, $octaves:literal) => {
        paste! {
            pub const [< DOUBLY_AUGMENTED_$ident:upper >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimplePitchInterval::[< DOUBLY_AUGMENTED_$simple:upper >],
            };
            pub const [< AUGMENTED_$ident:upper >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimplePitchInterval::[< AUGMENTED_$simple:upper >],
            };
            pub const [< MAJOR_$ident:upper >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimplePitchInterval::[< MAJOR_$simple:upper >],
            };
            pub const [< MINOR_$ident:upper >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimplePitchInterval::[< MINOR_$simple:upper >],
            };
            pub const [< DIMINISHED_$ident:upper >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimplePitchInterval::[< DIMINISHED_$simple:upper >],
            };
            pub const [< DOUBLY_DIMINISHED_$ident:upper >]: Self = Self {
                octaves: $octaves,
                simple: UnorderedSimplePitchInterval::[< DOUBLY_DIMINISHED_$simple:upper >],
            };
        }
    };
}

impl UnorderedPitchInterval {
    #[doc(alias = "HALF_STEP")]
    pub const SEMITONE: Self = Self {
        octaves: 0,
        simple: UnorderedSimplePitchInterval::SEMITONE,
    };

    #[doc(alias = "WHOLE_TONE")]
    #[doc(alias = "STEP")]
    #[doc(alias = "WHOLE_STEP")]
    pub const TONE: Self = Self {
        octaves: 0,
        simple: UnorderedSimplePitchInterval::TONE,
    };

    make_unordered_pitch_interval_consts!(Perfect, UNISON, Unison, 0);
    make_unordered_pitch_interval_consts!(MajorMinor, SECOND, Second, 0);
    make_unordered_pitch_interval_consts!(MajorMinor, THIRD, Third, 0);
    make_unordered_pitch_interval_consts!(Perfect, FOURTH, Fourth, 0);
    make_unordered_pitch_interval_consts!(Perfect, FIFTH, Fifth, 0);
    make_unordered_pitch_interval_consts!(MajorMinor, SIXTH, Sixth, 0);
    make_unordered_pitch_interval_consts!(MajorMinor, SEVENTH, Seventh, 0);

    pub const DOUBLY_DIMINISHED_OCTAVE: Self = Self {
        octaves: 1,
        simple: UnorderedSimplePitchInterval::DOUBLY_DIMINISHED_UNISON,
    };

    pub const DIMINISHED_OCTAVE: Self = Self {
        octaves: 1,
        simple: UnorderedSimplePitchInterval::DIMINISHED_UNISON,
    };

    #[doc(alias = "OCTAVE")]
    pub const PERFECT_OCTAVE: Self = Self {
        octaves: 1,
        simple: UnorderedSimplePitchInterval::PERFECT_UNISON,
    };

    pub const AUGMENTED_OCTAVE: Self = Self {
        octaves: 1,
        simple: UnorderedSimplePitchInterval::AUGMENTED_UNISON,
    };

    pub const DOUBLY_AUGMENTED_OCTAVE: Self = Self {
        octaves: 1,
        simple: UnorderedSimplePitchInterval::DOUBLY_AUGMENTED_UNISON,
    };

    make_unordered_pitch_interval_consts!(MajorMinor, NINTH, Second, 1);
    make_unordered_pitch_interval_consts!(MajorMinor, TENTH, Third, 1);
    make_unordered_pitch_interval_consts!(Perfect, ELEVENTH, Fourth, 1);
    make_unordered_pitch_interval_consts!(Perfect, TWELFTH, Fifth, 1);
    make_unordered_pitch_interval_consts!(MajorMinor, THIRTEENTH, Sixth, 1);
    make_unordered_pitch_interval_consts!(MajorMinor, FOURTEENTH, Seventh, 1);

    #[doc(alias = "DOUBLE_OCTAVE")]
    pub const PERFECT_DOUBLE_OCTAVE: Self = Self {
        octaves: 2,
        simple: UnorderedSimplePitchInterval::PERFECT_UNISON,
    };

    pub const fn interval_number(&self) -> UnorderedPitchIntervalNumber {
        let Self { octaves, simple } = self;

        UnorderedPitchIntervalNumber {
            octaves: *octaves,
            simple: simple.interval_number(),
        }
    }

    pub fn quality(&self) -> IntervalQuality {
        self.simple.quality()
    }

    pub const fn ascending(self) -> OrderedPitchInterval {
        OrderedPitchInterval {
            direction: IntervalDirection::Ascending,
            unordered: self,
        }
    }

    pub const fn descending(self) -> OrderedPitchInterval {
        OrderedPitchInterval {
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
}

impl Enharmonic for UnorderedPitchInterval {
    fn enharmonic(&self, other: &Self) -> bool {
        TET12::semitones(self) == TET12::semitones(other)
    }
}

impl From<UnorderedSimplePitchInterval> for UnorderedPitchInterval {
    fn from(simple: UnorderedSimplePitchInterval) -> Self {
        Self { octaves: 0, simple }
    }
}

impl Display for UnorderedPitchInterval {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.quality().fmt(f)?;

        if f.alternate() {
            " ".fmt(f)?;
        }

        self.interval_number().fmt(f)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntervalDirection {
    Descending,
    Ascending,
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

#[derive(Debug, Clone, Copy, Hash)]
pub struct OrderedPitchIntervalNumber {
    pub direction: IntervalDirection,
    pub unordered: UnorderedPitchIntervalNumber,
}

impl Display for OrderedPitchIntervalNumber {
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

#[derive(Debug, Clone, Copy, Eq, Hash)]
pub struct OrderedPitchInterval {
    pub direction: IntervalDirection,
    pub unordered: UnorderedPitchInterval,
}

impl OrderedPitchInterval {
    pub const fn interval_number(&self) -> OrderedPitchIntervalNumber {
        let Self {
            direction,
            unordered,
        } = self;

        OrderedPitchIntervalNumber {
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

impl PartialEq for OrderedPitchInterval {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Self {
                    direction,
                    unordered:
                        UnorderedPitchInterval {
                            octaves: 0,
                            simple: UnorderedSimplePitchInterval::Unison(unison_quality),
                        },
                },
                Self {
                    direction: other_direction,
                    unordered:
                        UnorderedPitchInterval {
                            octaves: 0,
                            simple: UnorderedSimplePitchInterval::Unison(other_unison_quality),
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

impl PartialOrd for OrderedPitchInterval {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OrderedPitchInterval {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (
                Self {
                    direction,
                    unordered:
                        UnorderedPitchInterval {
                            octaves: 0,
                            simple: UnorderedSimplePitchInterval::Unison(unison_quality),
                        },
                },
                Self {
                    direction: other_direction,
                    unordered:
                        UnorderedPitchInterval {
                            octaves: 0,
                            simple: UnorderedSimplePitchInterval::Unison(other_unison_quality),
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

impl Enharmonic for OrderedPitchInterval {
    fn enharmonic(&self, other: &Self) -> bool {
        TET12::semitones(self) == TET12::semitones(other)
    }
}

impl Neg for OrderedPitchInterval {
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

impl Display for OrderedPitchInterval {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self {
                direction: _,
                unordered: UnorderedPitchInterval::PERFECT_UNISON,
            } => UnorderedPitchInterval::PERFECT_UNISON.fmt(f),
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

#[cfg(test)]
mod tests {
    use quickcheck_macros::quickcheck;

    use crate::{
        enharmonic::{assert_enharmonic, assert_not_enharmonic},
        pitches::Pitch,
    };

    use super::*;

    #[test]
    fn pitch_interval_number_ordering_examples() {
        assert!(UnorderedPitchIntervalNumber::UNISON < UnorderedPitchIntervalNumber::SECOND);
        assert!(UnorderedPitchIntervalNumber::THIRD < UnorderedPitchIntervalNumber::SEVENTH);
        assert!(UnorderedPitchIntervalNumber::UNISON < UnorderedPitchIntervalNumber::OCTAVE);
        assert!(UnorderedPitchIntervalNumber::THIRD < UnorderedPitchIntervalNumber::NINTH);
    }

    #[test]
    fn pitch_interval_from_one_based_examples() {
        assert_eq!(UnorderedPitchIntervalNumber::try_from_one_based(0), Err(()));

        assert_eq!(
            UnorderedPitchIntervalNumber::try_from_one_based(1),
            Ok(UnorderedPitchIntervalNumber::UNISON)
        );

        assert_eq!(
            UnorderedPitchIntervalNumber::try_from_one_based(4),
            Ok(UnorderedPitchIntervalNumber::FOURTH)
        );

        assert_eq!(
            UnorderedPitchIntervalNumber::try_from_one_based(8),
            Ok(UnorderedPitchIntervalNumber::OCTAVE)
        );

        assert_eq!(
            UnorderedPitchIntervalNumber::try_from_one_based(13),
            Ok(UnorderedPitchIntervalNumber::THIRTEENTH)
        );
    }

    #[test]
    fn ordered_pitch_interval_unison_equality_examples() {
        assert_eq!(
            UnorderedPitchInterval::PERFECT_UNISON.ascending(),
            UnorderedPitchInterval::PERFECT_UNISON.ascending()
        );
        assert_eq!(
            UnorderedPitchInterval::PERFECT_UNISON.ascending(),
            UnorderedPitchInterval::PERFECT_UNISON.descending()
        );
        assert_eq!(
            UnorderedPitchInterval::PERFECT_UNISON.descending(),
            UnorderedPitchInterval::PERFECT_UNISON.ascending()
        );
        assert_eq!(
            UnorderedPitchInterval::PERFECT_UNISON.descending(),
            UnorderedPitchInterval::PERFECT_UNISON.descending()
        );

        assert_eq!(
            UnorderedPitchInterval::AUGMENTED_UNISON.ascending(),
            UnorderedPitchInterval::DIMINISHED_UNISON.descending()
        );
        assert_eq!(
            UnorderedPitchInterval::AUGMENTED_UNISON.descending(),
            UnorderedPitchInterval::DIMINISHED_UNISON.ascending()
        );
        assert_ne!(
            UnorderedPitchInterval::AUGMENTED_UNISON.ascending(),
            UnorderedPitchInterval::DIMINISHED_UNISON.ascending()
        );
        assert_ne!(
            UnorderedPitchInterval::AUGMENTED_UNISON.descending(),
            UnorderedPitchInterval::DIMINISHED_UNISON.descending()
        );
    }

    #[test]
    fn ordered_pitch_interval_ordering_examples() {
        assert_eq!(
            UnorderedPitchInterval::PERFECT_UNISON
                .ascending()
                .cmp(&UnorderedPitchInterval::PERFECT_UNISON.ascending()),
            std::cmp::Ordering::Equal,
        );
        assert_eq!(
            UnorderedPitchInterval::DIMINISHED_UNISON
                .ascending()
                .cmp(&UnorderedPitchInterval::PERFECT_UNISON.ascending()),
            std::cmp::Ordering::Less,
        );
        assert_eq!(
            UnorderedPitchInterval::DIMINISHED_UNISON
                .ascending()
                .cmp(&UnorderedPitchInterval::AUGMENTED_UNISON.ascending()),
            std::cmp::Ordering::Less,
        );
        assert_eq!(
            UnorderedPitchInterval::DIMINISHED_UNISON
                .descending()
                .cmp(&UnorderedPitchInterval::AUGMENTED_UNISON.ascending()),
            std::cmp::Ordering::Equal,
        );
        assert_eq!(
            UnorderedPitchInterval::DIMINISHED_UNISON
                .descending()
                .cmp(&UnorderedPitchInterval::AUGMENTED_UNISON.descending()),
            std::cmp::Ordering::Greater,
        );

        assert_eq!(
            UnorderedPitchInterval::MAJOR_SECOND
                .descending()
                .cmp(&UnorderedPitchInterval::PERFECT_UNISON.ascending()),
            std::cmp::Ordering::Less,
        );
        assert_eq!(
            UnorderedPitchInterval::MAJOR_SECOND
                .descending()
                .cmp(&UnorderedPitchInterval::MAJOR_SECOND.ascending()),
            std::cmp::Ordering::Less,
        );

        assert_eq!(
            UnorderedPitchInterval::MAJOR_SECOND
                .ascending()
                .cmp(&UnorderedPitchInterval::MINOR_THIRD.ascending()),
            std::cmp::Ordering::Less,
        );
        assert_eq!(
            UnorderedPitchInterval::AUGMENTED_FIFTH
                .ascending()
                .cmp(&UnorderedPitchInterval::MINOR_SIXTH.ascending()),
            std::cmp::Ordering::Less,
        );
        assert_eq!(
            UnorderedPitchInterval::AUGMENTED_FIFTH
                .ascending()
                .cmp(&UnorderedPitchInterval::DIMINISHED_SIXTH.ascending()),
            std::cmp::Ordering::Less,
        );

        assert_eq!(
            UnorderedPitchInterval::MAJOR_THIRD
                .descending()
                .cmp(&UnorderedPitchInterval::PERFECT_FIFTH.descending()),
            std::cmp::Ordering::Greater,
        );
        assert_eq!(
            UnorderedPitchInterval::MAJOR_THIRD
                .descending()
                .cmp(&UnorderedPitchInterval::DOUBLY_AUGMENTED_FOURTH.descending()),
            std::cmp::Ordering::Greater,
        );
    }

    #[quickcheck]
    fn ordered_pitch_interval_ordering_respects_negation(
        a: OrderedPitchInterval,
        b: OrderedPitchInterval,
    ) {
        assert_eq!((-a).cmp(&-b), a.cmp(&b).reverse());
    }

    #[quickcheck]
    fn ordered_pitch_interval_eq_agrees_with_ord(a: OrderedPitchInterval, b: OrderedPitchInterval) {
        assert_eq!(a == b, a.cmp(&b) == std::cmp::Ordering::Equal);
    }

    #[test]
    fn ordered_pitch_interval_display_examples() {
        assert_eq!(
            format!("{}", UnorderedPitchInterval::PERFECT_UNISON.ascending()),
            "P1"
        );

        assert_eq!(
            format!("{}", UnorderedPitchInterval::MAJOR_NINTH.ascending()),
            "+M9"
        );

        assert_eq!(
            format!("{}", UnorderedPitchInterval::MINOR_SEVENTH.descending()),
            "-m7"
        );

        assert_eq!(
            format!("{}", UnorderedPitchInterval::AUGMENTED_FIFTH.descending()),
            "-A5"
        );

        assert_eq!(
            format!(
                "{}",
                UnorderedPitchInterval::DOUBLY_DIMINISHED_ELEVENTH.ascending()
            ),
            "+dd11"
        );

        assert_eq!(
            format!("{:#}", UnorderedPitchInterval::AUGMENTED_UNISON.ascending()),
            "ascending augmented unison"
        );

        assert_eq!(
            format!("{:#}", UnorderedPitchInterval::PERFECT_OCTAVE.ascending()),
            "ascending perfect octave"
        );

        assert_eq!(
            format!("{:#}", UnorderedPitchInterval::AUGMENTED_OCTAVE.ascending()),
            "ascending augmented octave"
        );

        assert_eq!(
            format!(
                "{:#}",
                UnorderedPitchInterval::PERFECT_DOUBLE_OCTAVE.descending()
            ),
            "descending perfect double octave"
        );

        assert_eq!(
            format!(
                "{:#}",
                UnorderedPitchInterval {
                    octaves: 3,
                    simple: UnorderedSimplePitchInterval::DIMINISHED_UNISON
                }
                .ascending()
            ),
            "ascending diminished 3x octave"
        );

        assert_eq!(
            format!("{:#}", UnorderedPitchInterval::MAJOR_THIRD.descending()),
            "descending major third"
        );

        assert_eq!(
            format!("{:#}", UnorderedPitchInterval::MINOR_NINTH.descending()),
            "descending minor ninth"
        );

        assert_eq!(
            format!(
                "{:#}",
                UnorderedPitchInterval::DOUBLY_AUGMENTED_FIFTH.ascending()
            ),
            "ascending doubly augmented fifth"
        );

        assert_eq!(
            format!(
                "{:#}",
                UnorderedPitchInterval::DOUBLY_DIMINISHED_SECOND
                    .diminish()
                    .diminish()
                    .descending()
            ),
            "descending 4x diminished second"
        );
    }

    #[quickcheck]
    fn ordered_pitch_interval_enharmonic_examples() {
        assert_enharmonic!(
            UnorderedPitchInterval::PERFECT_UNISON.ascending(),
            UnorderedPitchInterval::PERFECT_UNISON.ascending()
        );

        assert_enharmonic!(
            UnorderedPitchInterval::AUGMENTED_THIRD.ascending(),
            UnorderedPitchInterval::PERFECT_FOURTH.ascending()
        );

        assert_enharmonic!(
            UnorderedPitchInterval::DOUBLY_DIMINISHED_SECOND.ascending(),
            UnorderedPitchInterval::MINOR_SECOND.descending()
        );

        assert_enharmonic!(
            UnorderedPitchInterval::AUGMENTED_FOURTH.descending(),
            UnorderedPitchInterval::DIMINISHED_FIFTH.descending()
        );

        assert_enharmonic!(
            UnorderedPitchInterval::DOUBLY_AUGMENTED_SEVENTH.ascending(),
            UnorderedPitchInterval::AUGMENTED_OCTAVE.ascending()
        );

        assert_not_enharmonic!(
            UnorderedPitchInterval::PERFECT_UNISON.ascending(),
            UnorderedPitchInterval::PERFECT_OCTAVE.ascending()
        );

        assert_not_enharmonic!(
            UnorderedPitchInterval::MAJOR_THIRD.ascending(),
            UnorderedPitchInterval::MAJOR_THIRD.descending()
        );
    }

    #[quickcheck]
    fn ordered_pitch_interval_enharmonic_to_self(interval: OrderedPitchInterval) {
        assert_enharmonic!(interval, interval);
    }

    #[quickcheck]
    fn ordered_pitch_interval_eq_implies_enharmonic(
        a: OrderedPitchInterval,
        b: OrderedPitchInterval,
    ) {
        if a == b {
            assert_enharmonic!(a, b);
        }
    }

    #[quickcheck]
    fn ordered_pitch_interval_enharmonic_augment_invariant(
        a: OrderedPitchInterval,
        b: OrderedPitchInterval,
    ) {
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
    fn ordered_pitch_interval_enharmonic_diminish_invariant(
        a: OrderedPitchInterval,
        b: OrderedPitchInterval,
    ) {
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
}
