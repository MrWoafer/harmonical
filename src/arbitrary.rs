#![cfg(test)]

use std::num::NonZeroUsize;

use quickcheck::Arbitrary;

use crate::{
    intervals::{
        IntervalDirection, MajorMinorIntervalQuality, OrderedPitchClassInterval,
        OrderedPitchClassIntervalNumber, OrderedPitchInterval, PerfectIntervalQuality,
        UnorderedPitchInterval, UnorderedPitchIntervalNumber, UnorderedSimplePitchInterval,
        UnorderedSimplePitchIntervalNumber,
    },
    pitches::{Accidental, Letter, Pitch, PitchClass},
};

impl Arbitrary for Letter {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        *g.choose(&[
            Self::A,
            Self::B,
            Self::C,
            Self::D,
            Self::E,
            Self::F,
            Self::G,
        ])
        .expect("the list is non-empty")
    }
}

impl Arbitrary for Accidental {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        let choices = &[
            Self::Sharp(
                NonZeroUsize::new(usize::arbitrary(g) % 100 + 1).expect("should be non-zero"),
            ),
            Self::Natural,
            Self::Flat(
                NonZeroUsize::new(usize::arbitrary(g) % 100 + 1).expect("should be non-zero"),
            ),
        ];

        *g.choose(choices).expect("the list is non-empty")
    }
}

impl Arbitrary for PitchClass {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        Self {
            letter: Arbitrary::arbitrary(g),
            accidental: Arbitrary::arbitrary(g),
        }
    }
}

impl Arbitrary for Pitch {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        Self {
            class: Arbitrary::arbitrary(g),
            octave: isize::arbitrary(g) % 100,
        }
    }
}

impl Arbitrary for MajorMinorIntervalQuality {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        let choices = &[
            Self::Major,
            Self::Minor,
            Self::Augmented(
                NonZeroUsize::new(usize::arbitrary(g) % 100 + 1).expect("should be non-zero"),
            ),
            Self::Diminished(
                NonZeroUsize::new(usize::arbitrary(g) % 100 + 1).expect("should be non-zero"),
            ),
        ];

        *g.choose(choices).expect("the list is non-empty")
    }
}

impl Arbitrary for PerfectIntervalQuality {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        let choices = &[
            Self::Perfect,
            Self::Augmented(
                NonZeroUsize::new(usize::arbitrary(g) % 100 + 1).expect("should be non-zero"),
            ),
            Self::Diminished(
                NonZeroUsize::new(usize::arbitrary(g) % 100 + 1).expect("should be non-zero"),
            ),
        ];

        *g.choose(choices).expect("the list is non-empty")
    }
}

impl Arbitrary for OrderedPitchClassIntervalNumber {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        *g.choose(&[
            Self::Unison,
            Self::Second,
            Self::Third,
            Self::Fourth,
            Self::Fifth,
            Self::Sixth,
            Self::Seventh,
            Self::Octave,
        ])
        .expect("the list is non-empty")
    }
}

impl Arbitrary for OrderedPitchClassInterval {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        match OrderedPitchClassIntervalNumber::arbitrary(g) {
            OrderedPitchClassIntervalNumber::Unison => Self::Unison(Arbitrary::arbitrary(g)),
            OrderedPitchClassIntervalNumber::Second => Self::Second(Arbitrary::arbitrary(g)),
            OrderedPitchClassIntervalNumber::Third => Self::Third(Arbitrary::arbitrary(g)),
            OrderedPitchClassIntervalNumber::Fourth => Self::Fourth(Arbitrary::arbitrary(g)),
            OrderedPitchClassIntervalNumber::Fifth => Self::Fifth(Arbitrary::arbitrary(g)),
            OrderedPitchClassIntervalNumber::Sixth => Self::Sixth(Arbitrary::arbitrary(g)),
            OrderedPitchClassIntervalNumber::Seventh => Self::Seventh(Arbitrary::arbitrary(g)),
            OrderedPitchClassIntervalNumber::Octave => Self::DiminishedOctave(
                NonZeroUsize::new(usize::arbitrary(g) % 100 + 1).expect("should be non-zero"),
            ),
        }
    }
}

impl Arbitrary for UnorderedSimplePitchIntervalNumber {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        *g.choose(&[
            Self::Unison,
            Self::Second,
            Self::Third,
            Self::Fourth,
            Self::Fifth,
            Self::Sixth,
            Self::Seventh,
        ])
        .expect("the list is non-empty")
    }
}

impl Arbitrary for UnorderedSimplePitchInterval {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        match UnorderedSimplePitchIntervalNumber::arbitrary(g) {
            UnorderedSimplePitchIntervalNumber::Unison => Self::Unison(Arbitrary::arbitrary(g)),
            UnorderedSimplePitchIntervalNumber::Second => Self::Second(Arbitrary::arbitrary(g)),
            UnorderedSimplePitchIntervalNumber::Third => Self::Third(Arbitrary::arbitrary(g)),
            UnorderedSimplePitchIntervalNumber::Fourth => Self::Fourth(Arbitrary::arbitrary(g)),
            UnorderedSimplePitchIntervalNumber::Fifth => Self::Fifth(Arbitrary::arbitrary(g)),
            UnorderedSimplePitchIntervalNumber::Sixth => Self::Sixth(Arbitrary::arbitrary(g)),
            UnorderedSimplePitchIntervalNumber::Seventh => Self::Seventh(Arbitrary::arbitrary(g)),
        }
    }
}

impl Arbitrary for UnorderedPitchIntervalNumber {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        Self {
            octaves: usize::arbitrary(g) % 100,
            simple: Arbitrary::arbitrary(g),
        }
    }
}

impl Arbitrary for UnorderedPitchInterval {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        Self {
            octaves: usize::arbitrary(g) % 100,
            simple: Arbitrary::arbitrary(g),
        }
    }
}

impl Arbitrary for IntervalDirection {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        *g.choose(&[Self::Ascending, Self::Descending])
            .expect("the list is non-empty")
    }
}

impl Arbitrary for OrderedPitchInterval {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        Self {
            direction: Arbitrary::arbitrary(g),
            unordered: Arbitrary::arbitrary(g),
        }
    }
}
