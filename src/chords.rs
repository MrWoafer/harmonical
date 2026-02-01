use std::fmt::Display;

use paste::paste;

use crate::{intervals::UnorderedSimpleInterval, pitches::PitchClass};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ChordSuspension {
    Sus2,
    Sus4,
}

impl ChordSuspension {
    pub const fn interval(&self) -> UnorderedSimpleInterval {
        match self {
            Self::Sus4 => UnorderedSimpleInterval::P4,
            Self::Sus2 => UnorderedSimpleInterval::M2,
        }
    }
}

impl Display for ChordSuspension {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Sus4 => write!(f, "sus4"),
            Self::Sus2 => write!(f, "sus2"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ChordThird {
    Minor,
    Major,
    Suspension(ChordSuspension),
}

impl ChordThird {
    pub const fn interval(&self) -> UnorderedSimpleInterval {
        match self {
            Self::Major => UnorderedSimpleInterval::M3,
            Self::Minor => UnorderedSimpleInterval::m3,
            Self::Suspension(suspension) => suspension.interval(),
        }
    }
}

impl PartialOrd for ChordThird {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ChordThird {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        fn index(x: &ChordThird) -> usize {
            match x {
                ChordThird::Suspension(ChordSuspension::Sus2) => 0,
                ChordThird::Minor => 1,
                ChordThird::Major => 2,
                ChordThird::Suspension(ChordSuspension::Sus4) => 3,
            }
        }

        index(self).cmp(&index(other))
    }
}

impl Display for ChordThird {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Major => {
                if f.alternate() {
                    write!(f, "maj")
                } else {
                    write!(f, "M")
                }
            }
            Self::Minor => {
                if f.alternate() {
                    write!(f, "min")
                } else {
                    write!(f, "m")
                }
            }
            Self::Suspension(suspension) => suspension.fmt(f),
        }
    }
}

impl From<ChordSuspension> for ChordThird {
    fn from(suspension: ChordSuspension) -> Self {
        Self::Suspension(suspension)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ChordFifth {
    Diminished,
    Perfect,
    Augmented,
}

impl ChordFifth {
    pub const fn interval(&self) -> UnorderedSimpleInterval {
        match self {
            Self::Diminished => UnorderedSimpleInterval::d5,
            Self::Perfect => UnorderedSimpleInterval::P5,
            Self::Augmented => UnorderedSimpleInterval::A5,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TriadQuality {
    /// `true` means diminished fifth; `false` means perfect fifth.
    Major(bool),
    /// `true` means augmented fifth; `false` means perfect fifth.
    Minor(bool),
    Augmented {
        suspension: Option<ChordSuspension>,
    },
    Diminished {
        suspension: Option<ChordSuspension>,
    },
    Sus4,
    Sus2,
}

impl TriadQuality {
    #[expect(non_upper_case_globals)]
    pub const maj: Self = Self::Major(false);
    #[expect(non_upper_case_globals)]
    pub const maj_b5: Self = Self::Major(true);

    #[expect(non_upper_case_globals)]
    pub const min: Self = Self::Minor(false);
    #[expect(non_upper_case_globals)]
    pub const min_s5: Self = Self::Minor(true);

    #[expect(non_upper_case_globals)]
    pub const aug: Self = Self::Augmented { suspension: None };
    #[expect(non_upper_case_globals)]
    pub const aug_sus4: Self = Self::Augmented {
        suspension: Some(ChordSuspension::Sus4),
    };
    #[expect(non_upper_case_globals)]
    pub const aug_sus2: Self = Self::Augmented {
        suspension: Some(ChordSuspension::Sus2),
    };

    #[expect(non_upper_case_globals)]
    pub const dim: Self = Self::Diminished { suspension: None };
    #[expect(non_upper_case_globals)]
    pub const dim_sus4: Self = Self::Diminished {
        suspension: Some(ChordSuspension::Sus4),
    };
    #[expect(non_upper_case_globals)]
    pub const dim_sus2: Self = Self::Diminished {
        suspension: Some(ChordSuspension::Sus2),
    };

    #[expect(non_upper_case_globals)]
    pub const sus4: Self = Self::Sus4;

    #[expect(non_upper_case_globals)]
    pub const sus2: Self = Self::Sus2;

    pub const fn third(&self) -> ChordThird {
        match self {
            TriadQuality::Major(_) => ChordThird::Major,
            TriadQuality::Minor(_) => ChordThird::Minor,
            TriadQuality::Augmented { suspension } => match suspension {
                Some(suspension) => ChordThird::Suspension(*suspension),
                None => ChordThird::Major,
            },
            TriadQuality::Diminished { suspension } => match suspension {
                Some(suspension) => ChordThird::Suspension(*suspension),
                None => ChordThird::Minor,
            },
            TriadQuality::Sus4 => ChordThird::Suspension(ChordSuspension::Sus4),
            TriadQuality::Sus2 => ChordThird::Suspension(ChordSuspension::Sus2),
        }
    }

    pub const fn fifth(&self) -> ChordFifth {
        match self {
            TriadQuality::Major(diminished_fifth) => {
                if *diminished_fifth {
                    ChordFifth::Diminished
                } else {
                    ChordFifth::Perfect
                }
            }
            TriadQuality::Minor(augmented_fifth) => {
                if *augmented_fifth {
                    ChordFifth::Augmented
                } else {
                    ChordFifth::Perfect
                }
            }
            TriadQuality::Augmented { suspension: _ } => ChordFifth::Augmented,
            TriadQuality::Diminished { suspension: _ } => ChordFifth::Diminished,
            TriadQuality::Sus4 | TriadQuality::Sus2 => ChordFifth::Perfect,
        }
    }
}

impl Display for TriadQuality {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TriadQuality::Major(diminished_fifth) => {
                if f.alternate() {
                    write!(f, "maj")?;
                } else {
                    write!(f, "")?;
                }

                if *diminished_fifth {
                    write!(f, "(b5)")?;
                }
            }
            TriadQuality::Minor(augmented_fifth) => {
                if f.alternate() {
                    write!(f, "min")?;
                } else {
                    write!(f, "m")?;
                }

                if *augmented_fifth {
                    write!(f, "(#5)")?;
                }
            }
            TriadQuality::Augmented { suspension } => {
                if f.alternate() {
                    write!(f, "aug")?;
                } else {
                    write!(f, "+")?;
                }

                match suspension {
                    None => {}
                    Some(suspension) => {
                        if f.alternate() {
                            write!(f, "({})", suspension)?;
                        } else {
                            write!(f, "{}", suspension)?;
                        }
                    }
                }
            }
            TriadQuality::Diminished { suspension } => {
                if f.alternate() {
                    write!(f, "dim")?;
                } else {
                    write!(f, "°")?;
                }

                match suspension {
                    None => {}
                    Some(suspension) => {
                        if f.alternate() {
                            write!(f, "({})", suspension)?;
                        } else {
                            write!(f, "{}", suspension)?;
                        }
                    }
                }
            }
            TriadQuality::Sus4 => {
                write!(f, "sus4")?;
            }
            TriadQuality::Sus2 => {
                write!(f, "sus2")?;
            }
        }

        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RootPositionTriad {
    pub root: PitchClass,
    pub quality: TriadQuality,
}

macro_rules! make_root_position_triad_consts_for_letter {
    ($letter:ident) => {
        paste! {
            make_root_position_triad_consts_for_pitch_class!([<$letter x>]);
            make_root_position_triad_consts_for_pitch_class!([<$letter s>]);
            make_root_position_triad_consts_for_pitch_class!($letter);
            make_root_position_triad_consts_for_pitch_class!([<$letter b>]);
            make_root_position_triad_consts_for_pitch_class!([<$letter bb>]);
        }
    };
}

macro_rules! make_root_position_triad_consts_for_pitch_class {
    ($pitch_class:ident) => {
        paste! {
            #[allow(non_upper_case_globals)]
            pub const $pitch_class: Self = Self {
                root: PitchClass::$pitch_class,
                quality: TriadQuality::maj,
            };
            #[expect(non_upper_case_globals)]
            pub const [<$pitch_class _b5>]: Self = Self {
                root: PitchClass::$pitch_class,
                quality: TriadQuality::maj_b5,
            };

            #[expect(non_upper_case_globals)]
            pub const [<$pitch_class m>]: Self = Self {
                root: PitchClass::$pitch_class,
                quality: TriadQuality::min,
            };
            #[expect(non_upper_case_globals)]
            pub const [<$pitch_class m_s5>]: Self = Self {
                root: PitchClass::$pitch_class,
                quality: TriadQuality::min_s5,
            };

            #[expect(non_upper_case_globals)]
            pub const [<$pitch_class aug>]: Self = Self {
                root: PitchClass::$pitch_class,
                quality: TriadQuality::aug,
            };
            #[expect(non_upper_case_globals)]
            pub const [<$pitch_class aug_sus4>]: Self = Self {
                root: PitchClass::$pitch_class,
                quality: TriadQuality::aug_sus4,
            };
            #[expect(non_upper_case_globals)]
            pub const [<$pitch_class aug_sus2>]: Self = Self {
                root: PitchClass::$pitch_class,
                quality: TriadQuality::aug_sus2,
            };

            #[expect(non_upper_case_globals)]
            pub const [<$pitch_class dim>]: Self = Self {
                root: PitchClass::$pitch_class,
                quality: TriadQuality::dim,
            };
            #[expect(non_upper_case_globals)]
            pub const [<$pitch_class dim_sus4>]: Self = Self {
                root: PitchClass::$pitch_class,
                quality: TriadQuality::dim_sus4,
            };
            #[expect(non_upper_case_globals)]
            pub const [<$pitch_class dim_sus2>]: Self = Self {
                root: PitchClass::$pitch_class,
                quality: TriadQuality::dim_sus2,
            };

            #[expect(non_upper_case_globals)]
            pub const [<$pitch_class sus4>]: Self = Self {
                root: PitchClass::$pitch_class,
                quality: TriadQuality::sus4,
            };

            #[expect(non_upper_case_globals)]
            pub const [<$pitch_class sus2>]: Self = Self {
                root: PitchClass::$pitch_class,
                quality: TriadQuality::sus2,
            };
        }
    };
}

impl RootPositionTriad {
    make_root_position_triad_consts_for_letter!(C);
    make_root_position_triad_consts_for_letter!(D);
    make_root_position_triad_consts_for_letter!(E);
    make_root_position_triad_consts_for_letter!(F);
    make_root_position_triad_consts_for_letter!(G);
    make_root_position_triad_consts_for_letter!(A);
    make_root_position_triad_consts_for_letter!(B);

    pub const fn third(&self) -> ChordThird {
        let Self { root: _, quality } = self;

        quality.third()
    }

    pub const fn fifth(&self) -> ChordFifth {
        let Self { root: _, quality } = self;

        quality.fifth()
    }

    pub fn pitches(&self) -> [PitchClass; 3] {
        [
            self.root,
            self.root.wrapping_add(self.third().interval()),
            self.root.wrapping_add(self.fifth().interval()),
        ]
    }
}

impl Display for RootPositionTriad {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { root, quality } = self;

        write!(f, "{}", root)?;
        quality.fmt(f)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn root_position_triad_display() {
        assert_eq!(format!("{}", RootPositionTriad::C), "C");
        assert_eq!(format!("{}", RootPositionTriad::Dm), "Dm");
        assert_eq!(format!("{}", RootPositionTriad::Esus4), "Esus4");
        assert_eq!(format!("{}", RootPositionTriad::Fsus2), "Fsus2");
        assert_eq!(format!("{}", RootPositionTriad::Gaug), "G+");
        assert_eq!(format!("{}", RootPositionTriad::Adim), "A°");
        assert_eq!(format!("{}", RootPositionTriad::B_b5), "B(b5)");
        assert_eq!(format!("{}", RootPositionTriad::Cbm_s5), "Cbm(#5)");
        assert_eq!(format!("{}", RootPositionTriad::Dsaug_sus4), "D#+sus4");
        assert_eq!(format!("{}", RootPositionTriad::Ebbaug_sus2), "Ebb+sus2");
        assert_eq!(format!("{}", RootPositionTriad::Fbdim_sus4), "Fb°sus4");
        assert_eq!(format!("{}", RootPositionTriad::Gxdim_sus2), "Gx°sus2");

        assert_eq!(format!("{:#}", RootPositionTriad::C), "Cmaj");
        assert_eq!(format!("{:#}", RootPositionTriad::Dm), "Dmin");
        assert_eq!(format!("{:#}", RootPositionTriad::Esus4), "Esus4");
        assert_eq!(format!("{:#}", RootPositionTriad::Fsus2), "Fsus2");
        assert_eq!(format!("{:#}", RootPositionTriad::Gaug), "Gaug");
        assert_eq!(format!("{:#}", RootPositionTriad::Adim), "Adim");
        assert_eq!(format!("{:#}", RootPositionTriad::B_b5), "Bmaj(b5)");
        assert_eq!(format!("{:#}", RootPositionTriad::Cbm_s5), "Cbmin(#5)");
        assert_eq!(
            format!("{:#}", RootPositionTriad::Dsaug_sus4),
            "D#aug(sus4)"
        );
        assert_eq!(
            format!("{:#}", RootPositionTriad::Ebbaug_sus2),
            "Ebbaug(sus2)"
        );
        assert_eq!(
            format!("{:#}", RootPositionTriad::Fbdim_sus4),
            "Fbdim(sus4)"
        );
        assert_eq!(
            format!("{:#}", RootPositionTriad::Gxdim_sus2),
            "Gxdim(sus2)"
        );
    }

    #[test]
    fn root_position_triad_pitches() {
        assert_eq!(
            RootPositionTriad::C.pitches(),
            [PitchClass::C, PitchClass::E, PitchClass::G]
        );

        assert_eq!(
            RootPositionTriad::Dm.pitches(),
            [PitchClass::D, PitchClass::F, PitchClass::A]
        );

        assert_eq!(
            RootPositionTriad::Ebdim.pitches(),
            [PitchClass::Eb, PitchClass::Gb, PitchClass::Bbb]
        );

        assert_eq!(
            RootPositionTriad::Faug.pitches(),
            [PitchClass::F, PitchClass::A, PitchClass::Cs]
        );

        assert_eq!(
            RootPositionTriad::Gssus4.pitches(),
            [PitchClass::Gs, PitchClass::Cs, PitchClass::Ds]
        );

        assert_eq!(
            RootPositionTriad::Asus2.pitches(),
            [PitchClass::A, PitchClass::B, PitchClass::E]
        );

        assert_eq!(
            RootPositionTriad::Bdim_sus2.pitches(),
            [PitchClass::B, PitchClass::Cs, PitchClass::F]
        );
    }
}
