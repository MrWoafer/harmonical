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
