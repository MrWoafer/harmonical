use std::{fmt::Display, num::NonZeroUsize, ops::Sub};

use paste::paste;

use crate::{
    enharmonic::Enharmonic,
    intervals::{
        IntervalDirection, MajorMinorIntervalQuality, OrderedInterval, PerfectIntervalQuality,
        UnorderedInterval, UnorderedSimpleInterval, UnorderedSimpleIntervalNumber,
    },
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Letter {
    C,
    D,
    E,
    F,
    G,
    A,
    B,
}

impl Letter {
    pub const fn index_within_octave(&self) -> usize {
        match self {
            Self::C => 0,
            Self::D => 1,
            Self::E => 2,
            Self::F => 3,
            Self::G => 4,
            Self::A => 5,
            Self::B => 6,
        }
    }

    pub const fn semitones_within_octave_tet12(&self) -> usize {
        match self {
            Self::C => 0,
            Self::D => 2,
            Self::E => 4,
            Self::F => 5,
            Self::G => 7,
            Self::A => 9,
            Self::B => 11,
        }
    }
}

impl Display for Letter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", char::from(self))
    }
}

impl From<Letter> for char {
    fn from(letter: Letter) -> Self {
        Self::from(&letter)
    }
}

impl From<&Letter> for char {
    fn from(letter: &Letter) -> Self {
        match letter {
            Letter::A => 'A',
            Letter::B => 'B',
            Letter::C => 'C',
            Letter::D => 'D',
            Letter::E => 'E',
            Letter::F => 'F',
            Letter::G => 'G',
        }
    }
}

impl Sub for Letter {
    type Output = UnorderedSimpleIntervalNumber;

    fn sub(self, rhs: Self) -> Self::Output {
        let interval_number = if self.index_within_octave() >= rhs.index_within_octave() {
            self.index_within_octave() - rhs.index_within_octave()
        } else {
            self.index_within_octave() + 7 - rhs.index_within_octave()
        };

        UnorderedSimpleIntervalNumber::try_from_zero_based(interval_number)
            .expect("number should be in valid range")
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Accidental {
    Flat(NonZeroUsize),
    Natural,
    Sharp(NonZeroUsize),
}

impl Accidental {
    fn semitones_tet12(&self) -> isize {
        match self {
            Self::Sharp(times) => times.get() as isize,
            Self::Natural => 0,
            Self::Flat(times) => -(times.get() as isize),
        }
    }

    pub const fn sharpen(self) -> Self {
        match self {
            Self::Sharp(times) => Self::Sharp(times.checked_add(1).expect(
                "realistically something shouldn't be sharpened enough times for an overflow to \
                occur",
            )),
            Self::Natural => Self::Sharp(NonZeroUsize::new(1).unwrap()),
            Self::Flat(times) => match times.get() {
                0 => unreachable!(),
                1 => Self::Natural,
                times @ 2.. => {
                    Self::Flat(NonZeroUsize::new(times - 1).expect("should be non-zero"))
                }
            },
        }
    }

    pub const fn flatten(self) -> Self {
        match self {
            Self::Sharp(times) => match times.get() {
                0 => unreachable!(),
                1 => Self::Natural,
                times @ 2.. => {
                    Self::Sharp(NonZeroUsize::new(times - 1).expect("should be non-zero"))
                }
            },
            Self::Natural => Self::Flat(NonZeroUsize::new(1).unwrap()),
            Self::Flat(times) => Self::Flat(times.checked_add(1).expect(
                "realistically something shouldn't be flattened enough times for an overflow to \
                occur",
            )),
        }
    }
}

impl PartialOrd for Accidental {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Accidental {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.semitones_tet12().cmp(&other.semitones_tet12())
    }
}

impl Display for Accidental {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Accidental::Sharp(times) => {
                if times.get() % 2 == 1 {
                    write!(f, "#")?;
                }

                write!(f, "{}", "x".repeat(times.get() / 2))
            }
            Accidental::Natural => write!(f, "{}", if f.alternate() { "♮" } else { "" }),
            Accidental::Flat(times) => write!(f, "{}", "b".repeat(times.get())),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PitchClass {
    pub letter: Letter,
    pub accidental: Accidental,
}

macro_rules! make_pitch_class_consts {
    ($letter:ident) => {
        paste! {
            #[expect(non_upper_case_globals)]
            pub const [<$letter x>]: Self = Self {
                letter: Letter::$letter,
                accidental: Accidental::Sharp(NonZeroUsize::new(2).unwrap()),
            };
            #[expect(non_upper_case_globals)]
            pub const [<$letter s>]: Self = Self {
                letter: Letter::$letter,
                accidental: Accidental::Sharp(NonZeroUsize::new(1).unwrap()),
            };
            pub const $letter: Self = Self {
                letter: Letter::$letter,
                accidental: Accidental::Natural,
            };
            #[expect(non_upper_case_globals)]
            pub const [<$letter b>]: Self = Self {
                letter: Letter::$letter,
                accidental: Accidental::Flat(NonZeroUsize::new(1).unwrap()),
            };
            #[expect(non_upper_case_globals)]
            pub const [<$letter bb>]: Self = Self {
                letter: Letter::$letter,
                accidental: Accidental::Flat(NonZeroUsize::new(2).unwrap()),
            };
        }
    };
}

impl PitchClass {
    make_pitch_class_consts!(A);
    make_pitch_class_consts!(B);
    make_pitch_class_consts!(C);
    make_pitch_class_consts!(D);
    make_pitch_class_consts!(E);
    make_pitch_class_consts!(F);
    make_pitch_class_consts!(G);

    pub const fn sharpen(self) -> Self {
        let Self { letter, accidental } = self;

        Self {
            letter,
            accidental: accidental.sharpen(),
        }
    }

    pub const fn flatten(self) -> Self {
        let Self { letter, accidental } = self;

        Self {
            letter,
            accidental: accidental.flatten(),
        }
    }

    fn semitones_within_octave_tet12_non_wrapping(&self) -> isize {
        let Self { letter, accidental } = self;

        letter.semitones_within_octave_tet12() as isize + accidental.semitones_tet12()
    }

    fn semitones_within_octave_tet12_wrapping(&self) -> isize {
        self.semitones_within_octave_tet12_non_wrapping()
            .rem_euclid(12)
    }
}

impl Enharmonic for PitchClass {
    fn enharmonic(&self, other: &Self) -> bool {
        self.semitones_within_octave_tet12_wrapping()
            == other.semitones_within_octave_tet12_wrapping()
    }
}

impl Display for PitchClass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { letter, accidental } = self;

        letter.fmt(f)?;
        accidental.fmt(f)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Pitch {
    pub octave: isize,
    pub class: PitchClass,
}

macro_rules! make_pitch_consts {
    ($letter:ident) => {
        make_pitch_consts_specific_octave!($letter, 0);
        make_pitch_consts_specific_octave!($letter, 1);
        make_pitch_consts_specific_octave!($letter, 2);
        make_pitch_consts_specific_octave!($letter, 3);
        make_pitch_consts_specific_octave!($letter, 4);
        make_pitch_consts_specific_octave!($letter, 5);
        make_pitch_consts_specific_octave!($letter, 6);
        make_pitch_consts_specific_octave!($letter, 7);
        make_pitch_consts_specific_octave!($letter, 8);
    };
}

macro_rules! make_pitch_consts_specific_octave {
    ($letter:ident, $octave:literal) => {
        paste! {
            #[expect(non_upper_case_globals)]
            pub const [<$letter x $octave>]: Self = Self { class: PitchClass::[<$letter x>], octave: $octave };
            #[expect(non_upper_case_globals)]
            pub const [<$letter s $octave>]: Self = Self { class: PitchClass::[<$letter s>], octave: $octave };
            pub const [<$letter $octave>]: Self = Self { class: PitchClass::$letter, octave: $octave };
            #[expect(non_upper_case_globals)]
            pub const [<$letter b $octave>]: Self = Self { class: PitchClass::[<$letter b>], octave: $octave };
            #[expect(non_upper_case_globals)]
            pub const [<$letter bb $octave>]: Self = Self { class: PitchClass::[<$letter bb>], octave: $octave };
        }
    };
}

impl Pitch {
    make_pitch_consts!(A);
    make_pitch_consts!(B);
    make_pitch_consts!(C);
    make_pitch_consts!(D);
    make_pitch_consts!(E);
    make_pitch_consts!(F);
    make_pitch_consts!(G);

    pub const fn letter(&self) -> Letter {
        self.class.letter
    }

    pub const fn accidental(&self) -> Accidental {
        self.class.accidental
    }

    pub const fn sharpen(self) -> Self {
        let Self { class, octave } = self;

        Self {
            class: class.sharpen(),
            octave,
        }
    }

    pub const fn flatten(self) -> Self {
        let Self { class, octave } = self;

        Self {
            class: class.flatten(),
            octave,
        }
    }

    pub const fn octave_up(self) -> Self {
        let Self { octave, class } = self;

        Self {
            octave: octave + 1,
            class,
        }
    }

    pub const fn octave_down(self) -> Self {
        let Self { octave, class } = self;

        Self {
            octave: octave - 1,
            class,
        }
    }

    fn semitones_tet12(&self) -> isize {
        let Self { octave, class } = self;

        octave * 12 + class.semitones_within_octave_tet12_non_wrapping()
    }
}

impl Enharmonic for Pitch {
    fn enharmonic(&self, other: &Self) -> bool {
        self.semitones_tet12() == other.semitones_tet12()
    }
}

impl Display for Pitch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { class, octave } = self;

        class.fmt(f)?;
        octave.fmt(f)
    }
}

impl Sub for Pitch {
    type Output = OrderedInterval;

    fn sub(self, rhs: Self) -> Self::Output {
        let direction = match self.cmp(&rhs) {
            std::cmp::Ordering::Less => IntervalDirection::Descending,
            std::cmp::Ordering::Equal | std::cmp::Ordering::Greater => IntervalDirection::Ascending,
        };

        fn letter_index(pitch: &Pitch) -> isize {
            pitch.octave * 7 + pitch.letter().index_within_octave() as isize
        }

        let self_letter_pitch_number = letter_index(&self);
        let rhs_letter_pitch_number = letter_index(&rhs);

        let octaves = self_letter_pitch_number.abs_diff(rhs_letter_pitch_number) / 7;

        let simple_number = match direction {
            IntervalDirection::Ascending => self.letter() - rhs.letter(),
            IntervalDirection::Descending => rhs.letter() - self.letter(),
        };

        let simple_pitch_number_difference = match direction {
            IntervalDirection::Ascending => self.semitones_tet12() - rhs.semitones_tet12(),
            IntervalDirection::Descending => rhs.semitones_tet12() - self.semitones_tet12(),
        } - 12 * octaves as isize;

        let simple = match simple_number {
            UnorderedSimpleIntervalNumber::Unison => UnorderedSimpleInterval::Unison(
                PerfectIntervalQuality::from_index(simple_pitch_number_difference),
            ),
            UnorderedSimpleIntervalNumber::Second => UnorderedSimpleInterval::Second(
                MajorMinorIntervalQuality::from_index(simple_pitch_number_difference - 1),
            ),
            UnorderedSimpleIntervalNumber::Third => UnorderedSimpleInterval::Third(
                MajorMinorIntervalQuality::from_index(simple_pitch_number_difference - 3),
            ),
            UnorderedSimpleIntervalNumber::Fourth => UnorderedSimpleInterval::Fourth(
                PerfectIntervalQuality::from_index(simple_pitch_number_difference - 5),
            ),
            UnorderedSimpleIntervalNumber::Fifth => UnorderedSimpleInterval::Fifth(
                PerfectIntervalQuality::from_index(simple_pitch_number_difference - 7),
            ),
            UnorderedSimpleIntervalNumber::Sixth => UnorderedSimpleInterval::Sixth(
                MajorMinorIntervalQuality::from_index(simple_pitch_number_difference - 8),
            ),
            UnorderedSimpleIntervalNumber::Seventh => UnorderedSimpleInterval::Seventh(
                MajorMinorIntervalQuality::from_index(simple_pitch_number_difference - 10),
            ),
        };

        OrderedInterval {
            direction,
            unordered: UnorderedInterval { octaves, simple },
        }
    }
}

#[cfg(test)]
mod tests {
    use std::num::NonZeroUsize;

    use quickcheck_macros::quickcheck;

    use crate::enharmonic::{assert_enharmonic, assert_not_enharmonic};

    use super::*;

    #[test]
    fn pitch_display_examples() {
        assert_eq!(Pitch::A0.to_string(), "A0");
        assert_eq!(format!("{:#}", Pitch::B1), "B♮1");
        assert_eq!(Pitch::Cs3.to_string(), "C#3");
        assert_eq!(Pitch::Dx4.to_string(), "Dx4");
        assert_eq!(Pitch::Eb5.to_string(), "Eb5");
        assert_eq!(Pitch::Fbb6.to_string(), "Fbb6");
        assert_eq!(Pitch::G7.to_string(), "G7");

        assert_eq!(
            Pitch {
                octave: -2,
                class: PitchClass::Cs
            }
            .to_string(),
            "C#-2"
        );

        assert_eq!(
            PitchClass {
                letter: Letter::C,
                accidental: Accidental::Sharp(NonZeroUsize::new(4).unwrap())
            }
            .to_string(),
            "Cxx"
        );

        assert_eq!(
            PitchClass {
                letter: Letter::C,
                accidental: Accidental::Sharp(NonZeroUsize::new(5).unwrap())
            }
            .to_string(),
            "C#xx"
        );
    }

    #[test]
    fn sharpen_pitch_examples() {
        assert_eq!(Pitch::As3.sharpen(), Pitch::Ax3);
        assert_eq!(Pitch::B2.sharpen(), Pitch::Bs2);
        assert_eq!(Pitch::Cb1.sharpen(), Pitch::C1);
        assert_eq!(Pitch::Dbb0.sharpen(), Pitch::Db0);
    }

    #[test]
    fn flatten_pitch_examples() {
        assert_eq!(Pitch::Ex8.flatten(), Pitch::Es8);
        assert_eq!(Pitch::Fs7.flatten(), Pitch::F7);
        assert_eq!(Pitch::G6.flatten(), Pitch::Gb6);
        assert_eq!(Pitch::Ab5.flatten(), Pitch::Abb5);
        assert_eq!(Pitch::C0.flatten(), Pitch::Cb0);
    }

    #[test]
    fn pitch_sub_examples() {
        assert_eq!(
            Pitch::A4 - Pitch::A4,
            UnorderedInterval::PERFECT_UNISON.ascending()
        );

        assert_eq!(
            Pitch::A4 - Pitch::A4,
            UnorderedInterval::PERFECT_UNISON.descending()
        );

        assert_eq!(
            Pitch::B3 - Pitch::A3,
            UnorderedInterval::MAJOR_SECOND.ascending()
        );

        assert_eq!(
            Pitch::F2 - Pitch::E2,
            UnorderedInterval::MINOR_SECOND.ascending()
        );

        assert_eq!(
            Pitch::E5 - Pitch::F4,
            UnorderedInterval::MAJOR_SEVENTH.ascending()
        );

        assert_eq!(
            Pitch::G1 - Pitch::D1,
            UnorderedInterval::PERFECT_FOURTH.ascending()
        );

        assert_eq!(
            Pitch::Ab6 - Pitch::E6,
            UnorderedInterval::DIMINISHED_FOURTH.ascending()
        );

        assert_eq!(
            Pitch::Gs7 - Pitch::Gb7,
            UnorderedInterval::DOUBLY_AUGMENTED_UNISON.ascending()
        );

        assert_eq!(
            Pitch::Cbb4 - Pitch::Cx4,
            UnorderedInterval::from(UnorderedSimpleInterval::Unison(
                PerfectIntervalQuality::Augmented(NonZeroUsize::new(4).unwrap())
            ))
            .descending()
        );

        assert_eq!(
            Pitch::Cbb5 - Pitch::Cx4,
            UnorderedInterval {
                octaves: 1,
                simple: UnorderedSimpleInterval::Unison(PerfectIntervalQuality::Diminished(
                    NonZeroUsize::new(4).unwrap()
                ))
            }
            .ascending()
        );

        assert_eq!(
            Pitch::Fx5 - Pitch::Fbb4,
            UnorderedInterval {
                octaves: 1,
                simple: UnorderedSimpleInterval::Unison(PerfectIntervalQuality::Augmented(
                    NonZeroUsize::new(4).unwrap()
                ))
            }
            .ascending()
        );

        assert_eq!(
            Pitch::Es5 - Pitch::As4,
            UnorderedInterval::PERFECT_FIFTH.ascending()
        );

        assert_eq!(
            Pitch::Es5 - Pitch::As3,
            UnorderedInterval::PERFECT_TWELFTH.ascending()
        );
    }

    #[quickcheck]
    fn pitch_sub_sharpen_invariant(a: Pitch, b: Pitch) {
        assert_eq!(a - b, a.sharpen() - b.sharpen());
    }

    #[quickcheck]
    fn pitch_sub_flatten_invariant(a: Pitch, b: Pitch) {
        assert_eq!(a - b, a.flatten() - b.flatten());
    }

    #[quickcheck]
    fn pitch_sub_octave_invariant(a: Pitch, b: Pitch) {
        assert_eq!(a - b, a.octave_up() - b.octave_up());
    }

    #[quickcheck]
    fn pitch_sub_anticommutative(a: Pitch, b: Pitch) {
        assert_eq!(a - b, -(b - a));
    }

    #[test]
    fn pitch_class_enharmonic_examples() {
        assert_enharmonic!(PitchClass::A, PitchClass::A);
        assert_enharmonic!(PitchClass::Ab, PitchClass::Gs);
        assert_enharmonic!(PitchClass::Cx, PitchClass::D);
        assert_enharmonic!(PitchClass::Fb, PitchClass::E);
        assert_enharmonic!(PitchClass::Bx, PitchClass::Cs);
        assert_enharmonic!(PitchClass::Cb, PitchClass::B);

        assert_not_enharmonic!(PitchClass::C, PitchClass::D);
        assert_not_enharmonic!(PitchClass::Gb, PitchClass::F);
        assert_not_enharmonic!(PitchClass::Ax, PitchClass::Bs);
    }

    #[quickcheck]
    fn pitch_class_enharmonic_to_self(pitch_class: PitchClass) {
        assert_enharmonic!(pitch_class, pitch_class);
    }

    #[quickcheck]
    fn pitch_class_eq_implies_enharmonic(a: PitchClass, b: PitchClass) {
        if a == b {
            assert_enharmonic!(a, b);
        }
    }

    #[test]
    fn pitch_enharmonic_examples() {
        assert_enharmonic!(Pitch::A4, Pitch::A4);
        assert_enharmonic!(Pitch::Ab3, Pitch::Gs3);
        assert_enharmonic!(Pitch::Cx2, Pitch::D2);
        assert_enharmonic!(Pitch::Fb5, Pitch::E5);
        assert_enharmonic!(Pitch::Bx2, Pitch::Cs3);
        assert_enharmonic!(Pitch::Cb5, Pitch::B4);

        assert_not_enharmonic!(Pitch::C3, Pitch::D3);
        assert_not_enharmonic!(Pitch::Gb4, Pitch::F4);
        assert_not_enharmonic!(Pitch::Ax6, Pitch::Bs6);
        assert_not_enharmonic!(Pitch::A4, Pitch::A5);
        assert_not_enharmonic!(Pitch::Cb5, Pitch::B5);
        assert_not_enharmonic!(Pitch::Bs3, Pitch::C3);
    }

    #[quickcheck]
    fn pitch_enharmonic_to_self(pitch: Pitch) {
        assert_enharmonic!(pitch, pitch);
    }

    #[quickcheck]
    fn pitch_eq_implies_enharmonic(a: Pitch, b: Pitch) {
        if a == b {
            assert_enharmonic!(a, b);
        }
    }

    #[quickcheck]
    fn pitch_enharmonic_sharpen_invariant(a: Pitch, b: Pitch) {
        assert_eq!(a.enharmonic(&b), a.sharpen().enharmonic(&b.sharpen()));
    }

    #[quickcheck]
    fn pitch_enharmonic_flatten_invariant(a: Pitch, b: Pitch) {
        assert_eq!(a.enharmonic(&b), a.flatten().enharmonic(&b.flatten()));
    }

    #[quickcheck]
    fn pitch_enharmonic_octave_invariant(a: Pitch, b: Pitch) {
        assert_eq!(a.enharmonic(&b), a.octave_up().enharmonic(&b.octave_up()));
    }

    #[quickcheck]
    fn pitch_enharmonic_implies_pitch_class_enharmonic(a: Pitch, b: Pitch) {
        if a.enharmonic(&b) {
            assert_enharmonic!(a.class, b.class);
        }
    }
}
