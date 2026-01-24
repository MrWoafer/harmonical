use std::{num::NonZeroUsize, ops::Neg};

use paste::paste;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MajorMinorQuality {
    Major,
    Minor,
    Augmented(NonZeroUsize),
    Diminished(NonZeroUsize),
}

impl MajorMinorQuality {
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
}

impl PartialOrd for MajorMinorQuality {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for MajorMinorQuality {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.index().cmp(&other.index())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PerfectQuality {
    Perfect,
    Augmented(NonZeroUsize),
    Diminished(NonZeroUsize),
}

impl PerfectQuality {
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
}

impl PartialOrd for PerfectQuality {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PerfectQuality {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.index().cmp(&other.index())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PitchClassIntervalNumber {
    Unison,
    Second,
    Third,
    Fourth,
    Fifth,
    Sixth,
    Seventh,
    Octave,
}

impl PitchClassIntervalNumber {
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OrderedPitchClassInterval {
    Unison(PerfectQuality),
    Second(MajorMinorQuality),
    Third(MajorMinorQuality),
    Fourth(PerfectQuality),
    Fifth(PerfectQuality),
    Sixth(MajorMinorQuality),
    Seventh(MajorMinorQuality),
    DiminishedOctave(NonZeroUsize),
}

macro_rules! make_ordered_pitch_class_interval_consts {
    (Perfect, $number:ident) => {
        paste! {
            pub const [< DOUBLY_ AUGMENTED_$number:upper >]: Self =
                Self::$number(PerfectQuality::Augmented(NonZeroUsize::new(2).unwrap()));
            pub const [< AUGMENTED_$number:upper >]: Self =
                Self::$number(PerfectQuality::Augmented(NonZeroUsize::new(1).unwrap()));
            pub const [< PERFECT_$number:upper >]: Self =
                Self::$number(PerfectQuality::Perfect);
            pub const [< DIMINISHED_$number:upper >]: Self =
                Self::$number(PerfectQuality::Diminished(NonZeroUsize::new(1).unwrap()));
            pub const [< DOUBLY_DIMINISHED_$number:upper >]: Self =
                Self::$number(PerfectQuality::Diminished(NonZeroUsize::new(2).unwrap()));
        }
    };
    (MajorMinor, $number:ident) => {
        paste! {
            pub const [< DOUBLY_AUGMENTED_$number:upper >]: Self =
                Self::$number(MajorMinorQuality::Augmented(NonZeroUsize::new(2).unwrap()));
            pub const [< AUGMENTED_$number:upper >]: Self =
                Self::$number(MajorMinorQuality::Augmented(NonZeroUsize::new(1).unwrap()));
            pub const [< MAJOR_$number:upper >]: Self =
                Self::$number(MajorMinorQuality::Major);
            pub const [< MINOR_$number:upper >]: Self =
                Self::$number(MajorMinorQuality::Minor);
            pub const [< DIMINISHED_$number:upper >]: Self =
                Self::$number(MajorMinorQuality::Diminished(NonZeroUsize::new(1).unwrap()));
            pub const [< DOUBLY_DIMINISHED_$number:upper >]: Self =
                Self::$number(MajorMinorQuality::Diminished(NonZeroUsize::new(2).unwrap()));
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

    make_ordered_pitch_class_interval_consts!(Perfect, Unison);
    make_ordered_pitch_class_interval_consts!(MajorMinor, Second);
    make_ordered_pitch_class_interval_consts!(MajorMinor, Third);
    make_ordered_pitch_class_interval_consts!(Perfect, Fourth);
    make_ordered_pitch_class_interval_consts!(Perfect, Fifth);
    make_ordered_pitch_class_interval_consts!(MajorMinor, Sixth);
    make_ordered_pitch_class_interval_consts!(MajorMinor, Seventh);

    pub const DIMINISHED_OCTAVE: Self = Self::DiminishedOctave(NonZeroUsize::new(1).unwrap());
    pub const DOUBLY_DIMINISHED_OCTAVE: Self =
        Self::DiminishedOctave(NonZeroUsize::new(2).unwrap());

    pub const fn interval_number(&self) -> PitchClassIntervalNumber {
        match self {
            Self::Unison(_) => PitchClassIntervalNumber::Unison,
            Self::Second(_) => PitchClassIntervalNumber::Second,
            Self::Third(_) => PitchClassIntervalNumber::Third,
            Self::Fourth(_) => PitchClassIntervalNumber::Fourth,
            Self::Fifth(_) => PitchClassIntervalNumber::Fifth,
            Self::Sixth(_) => PitchClassIntervalNumber::Sixth,
            Self::Seventh(_) => PitchClassIntervalNumber::Seventh,
            Self::DiminishedOctave(_) => PitchClassIntervalNumber::Octave,
        }
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnorderedSimplePitchInterval {
    Unison(PerfectQuality),
    Second(MajorMinorQuality),
    Third(MajorMinorQuality),
    Fourth(PerfectQuality),
    Fifth(PerfectQuality),
    Sixth(MajorMinorQuality),
    Seventh(MajorMinorQuality),
}

macro_rules! make_unordered_simple_pitch_interval_consts {
    (Perfect, $number:ident) => {
        paste! {
            pub const [< DOUBLY_ AUGMENTED_$number:upper >]: Self =
                Self::$number(PerfectQuality::Augmented(NonZeroUsize::new(2).unwrap()));
            pub const [< AUGMENTED_$number:upper >]: Self =
                Self::$number(PerfectQuality::Augmented(NonZeroUsize::new(1).unwrap()));
            pub const [< PERFECT_$number:upper >]: Self =
                Self::$number(PerfectQuality::Perfect);
            pub const [< DIMINISHED_$number:upper >]: Self =
                Self::$number(PerfectQuality::Diminished(NonZeroUsize::new(1).unwrap()));
            pub const [< DOUBLY_DIMINISHED_$number:upper >]: Self =
                Self::$number(PerfectQuality::Diminished(NonZeroUsize::new(2).unwrap()));
        }
    };
    (MajorMinor, $number:ident) => {
        paste! {
            pub const [< DOUBLY_AUGMENTED_$number:upper >]: Self =
                Self::$number(MajorMinorQuality::Augmented(NonZeroUsize::new(2).unwrap()));
            pub const [< AUGMENTED_$number:upper >]: Self =
                Self::$number(MajorMinorQuality::Augmented(NonZeroUsize::new(1).unwrap()));
            pub const [< MAJOR_$number:upper >]: Self =
                Self::$number(MajorMinorQuality::Major);
            pub const [< MINOR_$number:upper >]: Self =
                Self::$number(MajorMinorQuality::Minor);
            pub const [< DIMINISHED_$number:upper >]: Self =
                Self::$number(MajorMinorQuality::Diminished(NonZeroUsize::new(1).unwrap()));
            pub const [< DOUBLY_DIMINISHED_$number:upper >]: Self =
                Self::$number(MajorMinorQuality::Diminished(NonZeroUsize::new(2).unwrap()));
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
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UnorderedPitchIntervalNumber {
    pub octaves: usize,
    pub simple: UnorderedSimplePitchIntervalNumber,
}

impl UnorderedPitchIntervalNumber {
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
}

impl From<UnorderedSimplePitchIntervalNumber> for UnorderedPitchIntervalNumber {
    fn from(simple: UnorderedSimplePitchIntervalNumber) -> Self {
        Self { octaves: 0, simple }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

    pub const OCTAVE: Self = Self {
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

    pub const DOUBLE_OCTAVE: Self = Self {
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
}

impl From<UnorderedSimplePitchInterval> for UnorderedPitchInterval {
    fn from(simple: UnorderedSimplePitchInterval) -> Self {
        Self { octaves: 0, simple }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntervalDirection {
    Ascending,
    Descending,
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

#[derive(Debug, Clone, Copy, Eq, Hash)]
pub struct OrderedPitchInterval {
    pub direction: IntervalDirection,
    pub unordered: UnorderedPitchInterval,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pitch_interval_number_ordering() {
        assert!(UnorderedPitchIntervalNumber::UNISON < UnorderedPitchIntervalNumber::SECOND);
        assert!(UnorderedPitchIntervalNumber::THIRD < UnorderedPitchIntervalNumber::SEVENTH);
        assert!(UnorderedPitchIntervalNumber::UNISON < UnorderedPitchIntervalNumber::OCTAVE);
        assert!(UnorderedPitchIntervalNumber::THIRD < UnorderedPitchIntervalNumber::NINTH);
    }

    #[test]
    fn pitch_interval_from_one_based() {
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
    fn unison_equality() {
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
}
