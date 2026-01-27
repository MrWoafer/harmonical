use std::{fmt::Display, num::NonZeroUsize, ops::Sub};

use paste::paste;

use crate::{
    enharmonic::Enharmonic,
    intervals::{
        IntervalDirection, MajorMinorIntervalQuality, OrderedPitchClassInterval,
        OrderedPitchClassIntervalNumber, OrderedPitchInterval, PerfectIntervalQuality,
        UnorderedPitchInterval, UnorderedSimplePitchInterval,
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
    pub const fn index_in_octave(&self) -> usize {
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
    type Output = OrderedPitchClassIntervalNumber;

    fn sub(self, rhs: Self) -> Self::Output {
        let interval_number = if self.index_in_octave() >= rhs.index_in_octave() {
            self.index_in_octave() - rhs.index_in_octave()
        } else {
            self.index_in_octave() + 7 - rhs.index_in_octave()
        };

        OrderedPitchClassIntervalNumber::try_from_zero_based(interval_number)
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
    fn index(&self) -> isize {
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
        self.index().cmp(&other.index())
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

    fn pitch_class_number(&self) -> isize {
        let Self { letter, accidental } = self;

        accidental.index()
            + match letter {
                Letter::C => 0,
                Letter::D => 2,
                Letter::E => 4,
                Letter::F => 5,
                Letter::G => 7,
                Letter::A => 9,
                Letter::B => 11,
            }
    }
}

impl Enharmonic for PitchClass {
    fn enharmonic(&self, other: &Self) -> bool {
        self.pitch_class_number().rem_euclid(12) == other.pitch_class_number().rem_euclid(12)
    }
}

impl Display for PitchClass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { letter, accidental } = self;

        letter.fmt(f)?;
        accidental.fmt(f)
    }
}
impl Sub for PitchClass {
    type Output = OrderedPitchClassInterval;

    fn sub(self, rhs: Self) -> Self::Output {
        let interval_number = if self.letter == rhs.letter && self.accidental < rhs.accidental {
            OrderedPitchClassIntervalNumber::Octave
        } else {
            self.letter - rhs.letter
        };

        let pitch_class_number_difference = if self.pitch_class_number() >= rhs.pitch_class_number()
        {
            self.pitch_class_number() as isize - rhs.pitch_class_number() as isize
        } else {
            self.pitch_class_number() as isize + 12 - rhs.pitch_class_number() as isize
        };

        println!(
            "{}: {}, {}: {}",
            self,
            self.pitch_class_number(),
            rhs,
            rhs.pitch_class_number()
        );

        match interval_number {
            OrderedPitchClassIntervalNumber::Unison => OrderedPitchClassInterval::Unison(
                PerfectIntervalQuality::from_index(pitch_class_number_difference),
            ),
            OrderedPitchClassIntervalNumber::Second => OrderedPitchClassInterval::Second(
                MajorMinorIntervalQuality::from_index(pitch_class_number_difference - 1),
            ),
            OrderedPitchClassIntervalNumber::Third => OrderedPitchClassInterval::Third(
                MajorMinorIntervalQuality::from_index(pitch_class_number_difference - 3),
            ),
            OrderedPitchClassIntervalNumber::Fourth => OrderedPitchClassInterval::Fourth(
                PerfectIntervalQuality::from_index(pitch_class_number_difference - 5),
            ),
            OrderedPitchClassIntervalNumber::Fifth => OrderedPitchClassInterval::Fifth(
                PerfectIntervalQuality::from_index(pitch_class_number_difference - 7),
            ),
            OrderedPitchClassIntervalNumber::Sixth => OrderedPitchClassInterval::Sixth(
                MajorMinorIntervalQuality::from_index(pitch_class_number_difference - 8),
            ),
            OrderedPitchClassIntervalNumber::Seventh => OrderedPitchClassInterval::Seventh(
                MajorMinorIntervalQuality::from_index(pitch_class_number_difference - 10),
            ),
            OrderedPitchClassIntervalNumber::Octave => OrderedPitchClassInterval::DiminishedOctave(
                NonZeroUsize::new(
                    usize::try_from(12 - pitch_class_number_difference)
                        .expect("pitch class number difference should be <= 11"),
                )
                .expect("pitch class number difference should be <= 11"),
            ),
        }
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

    fn pitch_number(&self) -> isize {
        let Self {
            octave,
            class: PitchClass { letter, accidental },
        } = self;

        octave * 12
            + match letter {
                Letter::C => 0,
                Letter::D => 2,
                Letter::E => 4,
                Letter::F => 5,
                Letter::G => 7,
                Letter::A => 9,
                Letter::B => 11,
            }
            + accidental.index()
    }
}

impl Enharmonic for Pitch {
    fn enharmonic(&self, other: &Self) -> bool {
        self.pitch_number() == other.pitch_number()
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
    type Output = OrderedPitchInterval;

    fn sub(self, rhs: Self) -> Self::Output {
        let direction = match self.cmp(&rhs) {
            std::cmp::Ordering::Less => IntervalDirection::Descending,
            std::cmp::Ordering::Equal | std::cmp::Ordering::Greater => IntervalDirection::Ascending,
        };

        fn letter_pitch_number(pitch: &Pitch) -> isize {
            pitch.octave * 7 + pitch.letter().index_in_octave() as isize
        }

        let self_letter_pitch_number = letter_pitch_number(&self);
        let rhs_letter_pitch_number = letter_pitch_number(&rhs);

        let octaves = self_letter_pitch_number.abs_diff(rhs_letter_pitch_number) / 7;

        let pitch_class_interval = match direction {
            IntervalDirection::Ascending => self.class - rhs.class,
            IntervalDirection::Descending => rhs.class - self.class,
        };

        let simple = match pitch_class_interval {
            OrderedPitchClassInterval::Unison(quality) => {
                UnorderedSimplePitchInterval::Unison(quality)
            }
            OrderedPitchClassInterval::Second(quality) => {
                UnorderedSimplePitchInterval::Second(quality)
            }
            OrderedPitchClassInterval::Third(quality) => {
                UnorderedSimplePitchInterval::Third(quality)
            }
            OrderedPitchClassInterval::Fourth(quality) => {
                UnorderedSimplePitchInterval::Fourth(quality)
            }
            OrderedPitchClassInterval::Fifth(quality) => {
                UnorderedSimplePitchInterval::Fifth(quality)
            }
            OrderedPitchClassInterval::Sixth(quality) => {
                UnorderedSimplePitchInterval::Sixth(quality)
            }
            OrderedPitchClassInterval::Seventh(quality) => {
                UnorderedSimplePitchInterval::Seventh(quality)
            }
            OrderedPitchClassInterval::DiminishedOctave(times) => {
                UnorderedSimplePitchInterval::Unison(PerfectIntervalQuality::Diminished(times))
            }
        };

        OrderedPitchInterval {
            direction,
            unordered: UnorderedPitchInterval { octaves, simple },
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
    fn pitch_class_sub_examples() {
        assert_eq!(
            PitchClass::A - PitchClass::A,
            OrderedPitchClassInterval::PERFECT_UNISON
        );

        assert_eq!(
            PitchClass::B - PitchClass::A,
            OrderedPitchClassInterval::MAJOR_SECOND
        );

        assert_eq!(
            PitchClass::F - PitchClass::E,
            OrderedPitchClassInterval::MINOR_SECOND
        );

        assert_eq!(
            PitchClass::E - PitchClass::F,
            OrderedPitchClassInterval::MAJOR_SEVENTH
        );

        assert_eq!(
            PitchClass::G - PitchClass::D,
            OrderedPitchClassInterval::PERFECT_FOURTH
        );

        assert_eq!(
            PitchClass::Ab - PitchClass::E,
            OrderedPitchClassInterval::DIMINISHED_FOURTH
        );

        assert_eq!(
            PitchClass::Gs - PitchClass::Gb,
            OrderedPitchClassInterval::DOUBLY_AUGMENTED_UNISON
        );

        assert_eq!(
            PitchClass::Cbb - PitchClass::Cx,
            OrderedPitchClassInterval::DiminishedOctave(NonZeroUsize::new(4).unwrap())
        );
    }

    #[quickcheck]
    fn pitch_class_sub_sharpen_invariant(a: PitchClass, b: PitchClass) {
        assert_eq!(a - b, a.sharpen() - b.sharpen())
    }

    #[quickcheck]
    fn pitch_class_sub_flatten_invariant(a: PitchClass, b: PitchClass) {
        assert_eq!(a - b, a.flatten() - b.flatten())
    }

    #[test]
    fn pitch_sub_examples() {
        assert_eq!(
            Pitch::A4 - Pitch::A4,
            UnorderedPitchInterval::PERFECT_UNISON.ascending()
        );

        assert_eq!(
            Pitch::A4 - Pitch::A4,
            UnorderedPitchInterval::PERFECT_UNISON.descending()
        );

        assert_eq!(
            Pitch::B3 - Pitch::A3,
            UnorderedPitchInterval::MAJOR_SECOND.ascending()
        );

        assert_eq!(
            Pitch::F2 - Pitch::E2,
            UnorderedPitchInterval::MINOR_SECOND.ascending()
        );

        assert_eq!(
            Pitch::E5 - Pitch::F4,
            UnorderedPitchInterval::MAJOR_SEVENTH.ascending()
        );

        assert_eq!(
            Pitch::G1 - Pitch::D1,
            UnorderedPitchInterval::PERFECT_FOURTH.ascending()
        );

        assert_eq!(
            Pitch::Ab6 - Pitch::E6,
            UnorderedPitchInterval::DIMINISHED_FOURTH.ascending()
        );

        assert_eq!(
            Pitch::Gs7 - Pitch::Gb7,
            UnorderedPitchInterval::DOUBLY_AUGMENTED_UNISON.ascending()
        );

        assert_eq!(
            Pitch::Cbb4 - Pitch::Cx4,
            UnorderedPitchInterval::from(UnorderedSimplePitchInterval::Unison(
                PerfectIntervalQuality::Augmented(NonZeroUsize::new(4).unwrap())
            ))
            .descending()
        );

        assert_eq!(
            Pitch::Cbb5 - Pitch::Cx4,
            UnorderedPitchInterval {
                octaves: 1,
                simple: UnorderedSimplePitchInterval::Unison(PerfectIntervalQuality::Diminished(
                    NonZeroUsize::new(4).unwrap()
                ))
            }
            .ascending()
        );

        assert_eq!(
            Pitch::Fx5 - Pitch::Fbb4,
            UnorderedPitchInterval {
                octaves: 1,
                simple: UnorderedSimplePitchInterval::Unison(PerfectIntervalQuality::Augmented(
                    NonZeroUsize::new(4).unwrap()
                ))
            }
            .ascending()
        );

        assert_eq!(
            Pitch::Es5 - Pitch::As4,
            UnorderedPitchInterval::PERFECT_FIFTH.ascending()
        );

        assert_eq!(
            Pitch::Es5 - Pitch::As3,
            UnorderedPitchInterval::PERFECT_TWELFTH.ascending()
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
