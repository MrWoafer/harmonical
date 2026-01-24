#![cfg(test)]

use quickcheck::Arbitrary;

use crate::pitches::{Accidental, Letter, Pitch, PitchClass};

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
        *g.choose(&[
            Self::DoubleSharp,
            Self::Sharp,
            Self::Natural,
            Self::Flat,
            Self::DoubleFlat,
        ])
        .expect("the list is non-empty")
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
