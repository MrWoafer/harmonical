use std::fmt::Display;

use paste::paste;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NoteLetter {
    A,
    B,
    C,
    D,
    E,
    F,
    G,
}

impl Display for NoteLetter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", char::from(self))
    }
}

impl From<NoteLetter> for char {
    fn from(value: NoteLetter) -> Self {
        Self::from(&value)
    }
}

impl From<&NoteLetter> for char {
    fn from(value: &NoteLetter) -> Self {
        match value {
            NoteLetter::A => 'A',
            NoteLetter::B => 'B',
            NoteLetter::C => 'C',
            NoteLetter::D => 'D',
            NoteLetter::E => 'E',
            NoteLetter::F => 'F',
            NoteLetter::G => 'G',
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
pub struct Note(pub NoteLetter, pub Accidental);

impl Display for Note {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self(letter, accidental) = self;

        letter.fmt(f)?;
        accidental.fmt(f)
    }
}

macro_rules! make_note_consts {
    ($letter:ident) => {
        paste! {
            #[expect(non_upper_case_globals)]
            pub const [<$letter x>]: Note = Note(NoteLetter::$letter, Accidental::DoubleSharp);
            #[expect(non_upper_case_globals)]
            pub const [<$letter s>]: Note = Note(NoteLetter::$letter, Accidental::Sharp);
            pub const $letter: Note = Note(NoteLetter::$letter, Accidental::Natural);
            #[expect(non_upper_case_globals)]
            pub const [<$letter b>]: Note = Note(NoteLetter::$letter, Accidental::Flat);
            #[expect(non_upper_case_globals)]
            pub const [<$letter bb>]: Note = Note(NoteLetter::$letter, Accidental::DoubleFlat);
        }
    };
}

impl Note {
    make_note_consts!(A);
    make_note_consts!(B);
    make_note_consts!(C);
    make_note_consts!(D);
    make_note_consts!(E);
    make_note_consts!(F);
    make_note_consts!(G);
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
