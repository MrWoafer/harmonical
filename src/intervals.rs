use std::{num::NonZeroUsize, ops::Neg};

use paste::paste;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MajorMinorQuality {
    Major,
    Minor,
    Augmented(NonZeroUsize),
    Diminished(NonZeroUsize),
}

impl PartialOrd for MajorMinorQuality {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for MajorMinorQuality {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        fn index(quality: &MajorMinorQuality) -> isize {
            match quality {
                MajorMinorQuality::Diminished(times) => -(times.get() as isize),
                MajorMinorQuality::Minor => 0,
                MajorMinorQuality::Major => 1,
                MajorMinorQuality::Augmented(times) => 1 + times.get() as isize,
            }
        }

        index(self).cmp(&index(other))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PerfectQuality {
    Perfect,
    Augmented(NonZeroUsize),
    Diminished(NonZeroUsize),
}

impl PartialOrd for PerfectQuality {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PerfectQuality {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        fn index(quality: &PerfectQuality) -> isize {
            match quality {
                PerfectQuality::Diminished(times) => -(times.get() as isize),
                PerfectQuality::Perfect => 0,
                PerfectQuality::Augmented(times) => times.get() as isize,
            }
        }

        index(self).cmp(&index(other))
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
}

impl PitchClassIntervalNumber {
    pub fn zero_based(&self) -> usize {
        match self {
            PitchClassIntervalNumber::Unison => 0,
            PitchClassIntervalNumber::Second => 1,
            PitchClassIntervalNumber::Third => 2,
            PitchClassIntervalNumber::Fourth => 3,
            PitchClassIntervalNumber::Fifth => 4,
            PitchClassIntervalNumber::Sixth => 5,
            PitchClassIntervalNumber::Seventh => 6,
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
pub enum OrderedPitchClassInterval {
    Unison(PerfectQuality),
    Second(MajorMinorQuality),
    Third(MajorMinorQuality),
    Fourth(PerfectQuality),
    Fifth(PerfectQuality),
    Sixth(MajorMinorQuality),
    Seventh(MajorMinorQuality),
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
                Self::$number(PerfectQuality::Augmented(NonZeroUsize::new(2).unwrap()));
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

    #[doc(alias = "TONE")]
    #[doc(alias = "STEP")]
    #[doc(alias = "WHOLE_STEP")]
    pub const WHOLE_TONE: Self = Self::MAJOR_SECOND;

    make_ordered_pitch_class_interval_consts!(Perfect, Unison);
    make_ordered_pitch_class_interval_consts!(MajorMinor, Second);
    make_ordered_pitch_class_interval_consts!(MajorMinor, Third);
    make_ordered_pitch_class_interval_consts!(Perfect, Fourth);
    make_ordered_pitch_class_interval_consts!(Perfect, Fifth);
    make_ordered_pitch_class_interval_consts!(MajorMinor, Sixth);
    make_ordered_pitch_class_interval_consts!(MajorMinor, Seventh);

    pub fn interval_number(&self) -> PitchClassIntervalNumber {
        match self {
            OrderedPitchClassInterval::Unison(_) => PitchClassIntervalNumber::Unison,
            OrderedPitchClassInterval::Second(_) => PitchClassIntervalNumber::Second,
            OrderedPitchClassInterval::Third(_) => PitchClassIntervalNumber::Third,
            OrderedPitchClassInterval::Fourth(_) => PitchClassIntervalNumber::Fourth,
            OrderedPitchClassInterval::Fifth(_) => PitchClassIntervalNumber::Fifth,
            OrderedPitchClassInterval::Sixth(_) => PitchClassIntervalNumber::Sixth,
            OrderedPitchClassInterval::Seventh(_) => PitchClassIntervalNumber::Seventh,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PitchIntervalNumber {
    pub octaves: usize,
    pub pitch_class_interval_number: PitchClassIntervalNumber,
}

impl PitchIntervalNumber {
    pub fn zero_based(&self) -> usize {
        let Self {
            octaves,
            pitch_class_interval_number,
        } = self;

        octaves * 7 + pitch_class_interval_number.zero_based()
    }

    pub fn one_based(&self) -> usize {
        self.zero_based() + 1
    }

    pub fn from_zero_based(number: usize) -> Self {
        Self {
            octaves: number / 7,
            pitch_class_interval_number: PitchClassIntervalNumber::try_from_zero_based(number % 7)
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

impl PitchIntervalNumber {
    pub const UNISON: Self = Self {
        octaves: 0,
        pitch_class_interval_number: PitchClassIntervalNumber::Unison,
    };

    pub const SECOND: Self = Self {
        octaves: 0,
        pitch_class_interval_number: PitchClassIntervalNumber::Second,
    };

    pub const THIRD: Self = Self {
        octaves: 0,
        pitch_class_interval_number: PitchClassIntervalNumber::Third,
    };

    pub const FOURTH: Self = Self {
        octaves: 0,
        pitch_class_interval_number: PitchClassIntervalNumber::Fourth,
    };

    pub const FIFTH: Self = Self {
        octaves: 0,
        pitch_class_interval_number: PitchClassIntervalNumber::Fifth,
    };

    pub const SIXTH: Self = Self {
        octaves: 0,
        pitch_class_interval_number: PitchClassIntervalNumber::Sixth,
    };

    pub const SEVENTH: Self = Self {
        octaves: 0,
        pitch_class_interval_number: PitchClassIntervalNumber::Seventh,
    };

    pub const OCTAVE: Self = Self {
        octaves: 1,
        pitch_class_interval_number: PitchClassIntervalNumber::Unison,
    };

    pub const NINTH: Self = Self {
        octaves: 1,
        pitch_class_interval_number: PitchClassIntervalNumber::Second,
    };

    pub const TENTH: Self = Self {
        octaves: 1,
        pitch_class_interval_number: PitchClassIntervalNumber::Third,
    };

    pub const ELEVENTH: Self = Self {
        octaves: 1,
        pitch_class_interval_number: PitchClassIntervalNumber::Fourth,
    };

    pub const TWELFTH: Self = Self {
        octaves: 1,
        pitch_class_interval_number: PitchClassIntervalNumber::Fifth,
    };

    pub const THIRTEENTH: Self = Self {
        octaves: 1,
        pitch_class_interval_number: PitchClassIntervalNumber::Sixth,
    };

    pub const FOURTEENTH: Self = Self {
        octaves: 1,
        pitch_class_interval_number: PitchClassIntervalNumber::Seventh,
    };
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnorderedPitchInterval {
    pub octaves: usize,
    pub ordered_pitch_class_interval: OrderedPitchClassInterval,
}

macro_rules! make_ordered_pitch_interval_consts {
    (Perfect, $number:ident) => {
        paste! {
            pub const [< DOUBLY_AUGMENTED_$number:upper >]: Self = Self {
                octaves: 0,
                ordered_pitch_class_interval: OrderedPitchClassInterval::[< DOUBLY_AUGMENTED_$number:upper >],
            };
            pub const [< AUGMENTED_$number:upper >]: Self = Self {
                octaves: 0,
                ordered_pitch_class_interval: OrderedPitchClassInterval::[< AUGMENTED_$number:upper >],
            };
            pub const [< PERFECT_$number:upper >]: Self = Self {
                octaves: 0,
                ordered_pitch_class_interval: OrderedPitchClassInterval::[< PERFECT_$number:upper >],
            };
            pub const [< DIMINISHED_$number:upper >]: Self = Self {
                octaves: 0,
                ordered_pitch_class_interval: OrderedPitchClassInterval::[< DIMINISHED_$number:upper >],
            };
            pub const [< DOUBLY_DIMINISHED_$number:upper >]: Self = Self {
                octaves: 0,
                ordered_pitch_class_interval: OrderedPitchClassInterval::[< DOUBLY_DIMINISHED_$number:upper >],
            };
        }
    };
    (MajorMinor, $number:ident) => {
        paste! {
            pub const [< DOUBLY_ AUGMENTED_$number:upper >]: Self = Self {
                octaves: 0,
                ordered_pitch_class_interval: OrderedPitchClassInterval::[< DOUBLY_AUGMENTED_$number:upper >],
            };
            pub const [< AUGMENTED_$number:upper >]: Self = Self {
                octaves: 0,
                ordered_pitch_class_interval: OrderedPitchClassInterval::[< AUGMENTED_$number:upper >],
            };
            pub const [< MAJOR_$number:upper >]: Self = Self {
                octaves: 0,
                ordered_pitch_class_interval: OrderedPitchClassInterval::[< MAJOR_$number:upper >],
            };
            pub const [< MINOR_$number:upper >]: Self = Self {
                octaves: 0,
                ordered_pitch_class_interval: OrderedPitchClassInterval::[< MINOR_$number:upper >],
            };
            pub const [< DIMINISHED_$number:upper >]: Self = Self {
                octaves: 0,
                ordered_pitch_class_interval: OrderedPitchClassInterval::[< DIMINISHED_$number:upper >],
            };
            pub const [< DOUBLY_DIMINISHED_$number:upper >]: Self = Self {
                octaves: 0,
                ordered_pitch_class_interval: OrderedPitchClassInterval::[< DOUBLY_DIMINISHED_$number:upper >],
            };
        }
    };
}

impl UnorderedPitchInterval {
    #[doc(alias = "HALF_STEP")]
    pub const SEMITONE: Self = Self {
        octaves: 0,
        ordered_pitch_class_interval: OrderedPitchClassInterval::SEMITONE,
    };

    #[doc(alias = "TONE")]
    #[doc(alias = "STEP")]
    #[doc(alias = "WHOLE_STEP")]
    pub const WHOLE_TONE: Self = Self {
        octaves: 0,
        ordered_pitch_class_interval: OrderedPitchClassInterval::WHOLE_TONE,
    };

    make_ordered_pitch_interval_consts!(Perfect, Unison);
    make_ordered_pitch_interval_consts!(MajorMinor, Second);
    make_ordered_pitch_interval_consts!(MajorMinor, Third);
    make_ordered_pitch_interval_consts!(Perfect, Fourth);
    make_ordered_pitch_interval_consts!(Perfect, Fifth);
    make_ordered_pitch_interval_consts!(MajorMinor, Sixth);
    make_ordered_pitch_interval_consts!(MajorMinor, Seventh);

    pub const OCTAVE: Self = Self {
        octaves: 1,
        ordered_pitch_class_interval: OrderedPitchClassInterval::PERFECT_UNISON,
    };

    pub fn interval_number(&self) -> PitchIntervalNumber {
        let Self {
            octaves,
            ordered_pitch_class_interval,
        } = self;

        PitchIntervalNumber {
            octaves: *octaves,
            pitch_class_interval_number: ordered_pitch_class_interval.interval_number(),
        }
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
                    direction: _,
                    unordered: UnorderedPitchInterval::PERFECT_UNISON,
                },
                Self {
                    direction: _,
                    unordered: UnorderedPitchInterval::PERFECT_UNISON,
                },
            ) => true,
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
        assert!(PitchIntervalNumber::UNISON < PitchIntervalNumber::SECOND);
        assert!(PitchIntervalNumber::THIRD < PitchIntervalNumber::SEVENTH);
        assert!(PitchIntervalNumber::UNISON < PitchIntervalNumber::OCTAVE);
        assert!(PitchIntervalNumber::THIRD < PitchIntervalNumber::NINTH);
    }

    #[test]
    fn pitch_interval_from_one_based() {
        assert_eq!(PitchIntervalNumber::try_from_one_based(0), Err(()));

        assert_eq!(
            PitchIntervalNumber::try_from_one_based(1),
            Ok(PitchIntervalNumber::UNISON)
        );

        assert_eq!(
            PitchIntervalNumber::try_from_one_based(4),
            Ok(PitchIntervalNumber::FOURTH)
        );

        assert_eq!(
            PitchIntervalNumber::try_from_one_based(8),
            Ok(PitchIntervalNumber::OCTAVE)
        );

        assert_eq!(
            PitchIntervalNumber::try_from_one_based(13),
            Ok(PitchIntervalNumber::THIRTEENTH)
        );
    }
}
