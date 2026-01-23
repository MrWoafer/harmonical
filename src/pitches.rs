use std::fmt::Display;

use paste::paste;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Letter {
    A,
    B,
    C,
    D,
    E,
    F,
    G,
}

impl Display for Letter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", char::from(self))
    }
}

impl From<Letter> for char {
    fn from(value: Letter) -> Self {
        Self::from(&value)
    }
}

impl From<&Letter> for char {
    fn from(value: &Letter) -> Self {
        match value {
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Accidental {
    DoubleSharp,
    Sharp,
    Natural,
    Flat,
    DoubleFlat,
}

impl Accidental {
    fn index(&self) -> isize {
        match self {
            Self::DoubleSharp => 2,
            Self::Sharp => 1,
            Self::Natural => 0,
            Self::Flat => -1,
            Self::DoubleFlat => -2,
        }
    }

    fn try_from_index(index: isize) -> Result<Self, ()> {
        match index {
            2 => Ok(Self::DoubleSharp),
            1 => Ok(Self::Sharp),
            0 => Ok(Self::Natural),
            -1 => Ok(Self::Flat),
            -2 => Ok(Self::DoubleFlat),
            _ => Err(()),
        }
    }

    pub fn try_sharpen(self) -> Result<Self, ()> {
        Self::try_from_index(self.index() + 1)
    }

    #[track_caller]
    pub fn sharpen(self) -> Self {
        self.try_sharpen().expect(&format!(
            "cannot sharpen {:?} as it cannot be represented by the type",
            self
        ))
    }

    pub fn try_flatten(self) -> Result<Self, ()> {
        Self::try_from_index(self.index() - 1)
    }

    #[track_caller]
    pub fn flatten(self) -> Self {
        self.try_flatten().expect(&format!(
            "cannot flatten {:?} as it cannot be represented by the type",
            self
        ))
    }
}

impl Display for Accidental {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Accidental::DoubleSharp => "x",
                Accidental::Sharp => "#",
                Accidental::Natural =>
                    if f.alternate() {
                        "♮"
                    } else {
                        ""
                    },
                Accidental::Flat => "b",
                Accidental::DoubleFlat => "bb",
            }
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
                accidental: Accidental::DoubleSharp,
            };
            #[expect(non_upper_case_globals)]
            pub const [<$letter s>]: Self = Self {
                letter: Letter::$letter,
                accidental: Accidental::Sharp,
            };
            pub const $letter: Self = Self {
                letter: Letter::$letter,
                accidental: Accidental::Natural,
            };
            #[expect(non_upper_case_globals)]
            pub const [<$letter b>]: Self = Self {
                letter: Letter::$letter,
                accidental: Accidental::Flat,
            };
            #[expect(non_upper_case_globals)]
            pub const [<$letter bb>]: Self = Self {
                letter: Letter::$letter,
                accidental: Accidental::DoubleFlat,
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

    pub fn try_sharpen(self) -> Result<Self, ()> {
        let Self { letter, accidental } = self;

        accidental
            .try_sharpen()
            .map(|accidental| Self { letter, accidental })
    }

    #[track_caller]
    pub fn sharpen(self) -> Self {
        let Self { letter, accidental } = self;

        Self {
            letter,
            accidental: accidental.sharpen(),
        }
    }

    pub fn try_flatten(self) -> Result<Self, ()> {
        let Self { letter, accidental } = self;

        accidental
            .try_flatten()
            .map(|accidental| Self { letter, accidental })
    }

    #[track_caller]
    pub fn flatten(self) -> Self {
        let Self { letter, accidental } = self;

        Self {
            letter,
            accidental: accidental.flatten(),
        }
    }
}

impl Display for PitchClass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { letter, accidental } = self;

        letter.fmt(f)?;
        accidental.fmt(f)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Pitch {
    pub class: PitchClass,
    pub octave: isize,
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

    pub fn try_sharpen(self) -> Result<Self, ()> {
        let Self { class, octave } = self;

        class.try_sharpen().map(|class| Self { class, octave })
    }

    #[track_caller]
    pub fn sharpen(self) -> Self {
        let Self { class, octave } = self;

        Self {
            class: class.sharpen(),
            octave,
        }
    }

    pub fn try_flatten(self) -> Result<Self, ()> {
        let Self { class, octave } = self;

        class.try_flatten().map(|class| Self { class, octave })
    }

    #[track_caller]
    pub fn flatten(self) -> Self {
        let Self { class, octave } = self;

        Self {
            class: class.flatten(),
            octave,
        }
    }
}

impl Display for Pitch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { class, octave } = self;

        class.fmt(f)?;
        octave.fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pitch_display() {
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
    }

    #[test]
    fn sharpen_pitch() {
        assert_eq!(Pitch::As3.sharpen(), Pitch::Ax3);
        assert_eq!(Pitch::B2.sharpen(), Pitch::Bs2);
        assert_eq!(Pitch::Cb1.sharpen(), Pitch::C1);
        assert_eq!(Pitch::Dbb0.sharpen(), Pitch::Db0);

        assert_eq!(Pitch::Ex5.try_sharpen(), Err(()));
    }

    #[test]
    fn flatten_pitch() {
        assert_eq!(Pitch::Ex8.flatten(), Pitch::Es8);
        assert_eq!(Pitch::Fs7.flatten(), Pitch::F7);
        assert_eq!(Pitch::G6.flatten(), Pitch::Gb6);
        assert_eq!(Pitch::Ab5.flatten(), Pitch::Abb5);
        assert_eq!(Pitch::C0.flatten(), Pitch::Cb0);

        assert_eq!(Pitch::Bbb2.try_flatten(), Err(()));
    }
}
