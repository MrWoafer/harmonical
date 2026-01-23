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

impl Display for PitchClass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { letter, accidental } = self;

        letter.fmt(f)?;
        accidental.fmt(f)
    }
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn note_display() {
        assert_eq!(Note::A.to_string(), "A");
        assert_eq!(format!("{:#}", Note::B), "B♮");
        assert_eq!(Note::Cs.to_string(), "C#");
        assert_eq!(Note::Dx.to_string(), "Dx");
        assert_eq!(Note::Eb.to_string(), "Eb");
        assert_eq!(Note::Fbb.to_string(), "Fbb");
        assert_eq!(Note::G.to_string(), "G");
    }
}
