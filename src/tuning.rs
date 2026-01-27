use crate::{
    intervals::{
        IntervalDirection, MajorMinorIntervalQuality, OrderedPitchClassInterval,
        OrderedPitchInterval, PerfectIntervalQuality, UnorderedPitchInterval,
        UnorderedSimplePitchInterval,
    },
    pitches::Pitch,
};

pub trait TuningSystem {
    fn hz(&self, pitch: &Pitch) -> f32;
}

/// 12-tone equal temperament.
#[derive(Debug, Clone, PartialEq)]
pub struct TET12 {
    /// The frequency of [`Pitch::A4`] in hertz.
    ///
    /// Must be finite and strictly positive.
    a4_hz: f32,
}

impl TET12 {
    /// The 12th root of 2.
    pub const RATIO: f32 = 1.05946309;

    pub const A440: Self = Self { a4_hz: 440.0 };

    pub const A432: Self = Self { a4_hz: 432.0 };

    pub const fn new(a4_hz: f32) -> Result<Self, ()> {
        if a4_hz.is_finite() && a4_hz > 0.0 {
            Ok(Self { a4_hz })
        } else {
            Err(())
        }
    }

    fn pow_ratio(pow: isize) -> f32 {
        2.0_f32.powi((pow / 12) as i32) * Self::RATIO.powi((pow % 12) as i32)
    }

    pub fn semitones<T>(of: &T) -> T::Semitones
    where
        T: SemitonesTET12,
    {
        of.semitones_tet12()
    }
}

impl TuningSystem for TET12 {
    fn hz(&self, pitch: &Pitch) -> f32 {
        self.a4_hz * Self::pow_ratio((*pitch - Pitch::A4).semitones_tet12())
    }
}

pub trait SemitonesTET12 {
    type Semitones;

    fn semitones_tet12(&self) -> Self::Semitones;
}

fn semitones_tet12_offset_major_minor(quality: &MajorMinorIntervalQuality) -> isize {
    match quality {
        MajorMinorIntervalQuality::Augmented(times) => times.get() as isize,
        MajorMinorIntervalQuality::Major => 0,
        MajorMinorIntervalQuality::Minor => -1,
        MajorMinorIntervalQuality::Diminished(times) => -1 - (times.get() as isize),
    }
}

fn semitones_tet12_offset_perfect(quality: &PerfectIntervalQuality) -> isize {
    match quality {
        PerfectIntervalQuality::Augmented(times) => times.get() as isize,
        PerfectIntervalQuality::Perfect => 0,
        PerfectIntervalQuality::Diminished(times) => -(times.get() as isize),
    }
}

impl SemitonesTET12 for OrderedPitchClassInterval {
    type Semitones = isize;

    fn semitones_tet12(&self) -> Self::Semitones {
        match self {
            Self::AugmentedUnison(times) => *times as isize,
            Self::Second(quality) => 2 + semitones_tet12_offset_major_minor(quality),
            Self::Third(quality) => 4 + semitones_tet12_offset_major_minor(quality),
            Self::Fourth(quality) => 5 + semitones_tet12_offset_perfect(quality),
            Self::Fifth(quality) => 7 + semitones_tet12_offset_perfect(quality),
            Self::Sixth(quality) => 9 + semitones_tet12_offset_major_minor(quality),
            Self::Seventh(quality) => 11 + semitones_tet12_offset_major_minor(quality),
            Self::DiminishedOctave(times) => 12 - times.get() as isize,
        }
    }
}

impl SemitonesTET12 for UnorderedSimplePitchInterval {
    type Semitones = isize;

    fn semitones_tet12(&self) -> Self::Semitones {
        match self {
            Self::Unison(quality) => 0 + semitones_tet12_offset_perfect(quality),
            Self::Second(quality) => 2 + semitones_tet12_offset_major_minor(quality),
            Self::Third(quality) => 4 + semitones_tet12_offset_major_minor(quality),
            Self::Fourth(quality) => 5 + semitones_tet12_offset_perfect(quality),
            Self::Fifth(quality) => 7 + semitones_tet12_offset_perfect(quality),
            Self::Sixth(quality) => 9 + semitones_tet12_offset_major_minor(quality),
            Self::Seventh(quality) => 11 + semitones_tet12_offset_major_minor(quality),
        }
    }
}

impl SemitonesTET12 for UnorderedPitchInterval {
    type Semitones = isize;

    fn semitones_tet12(&self) -> Self::Semitones {
        let Self { octaves, simple } = self;

        *octaves as isize * 12 + simple.semitones_tet12()
    }
}

impl SemitonesTET12 for OrderedPitchInterval {
    type Semitones = isize;

    fn semitones_tet12(&self) -> Self::Semitones {
        let Self {
            direction,
            unordered,
        } = self;

        let sign = match direction {
            IntervalDirection::Descending => -1,
            IntervalDirection::Ascending => 1,
        };

        sign * unordered.semitones_tet12()
    }
}

#[cfg(test)]
mod tests {
    use approx::assert_abs_diff_eq;
    use quickcheck_macros::quickcheck;

    use crate::enharmonic::Enharmonic;

    use super::*;

    #[test]
    fn tet12_hz() {
        assert_eq!(TET12::A440.hz(&Pitch::A4), 440.0);
        assert_eq!(TET12::A440.hz(&Pitch::A5), 880.0);
        assert_eq!(TET12::A440.hz(&Pitch::A3), 220.0);
        assert_eq!(TET12::A440.hz(&Pitch::A2), 110.0);

        assert_eq!(TET12::A432.hz(&Pitch::A4), 432.0);
        assert_eq!(TET12::A432.hz(&Pitch::A5), 864.0);
        assert_eq!(TET12::A432.hz(&Pitch::A3), 216.0);
        assert_eq!(TET12::A432.hz(&Pitch::A2), 108.0);

        // Values obtained from Wikipedia on the pages "$note (musical note)"
        assert_abs_diff_eq!(TET12::A440.hz(&Pitch::C4), 261.626, epsilon = 0.001);
        assert_abs_diff_eq!(TET12::A440.hz(&Pitch::D4), 293.665, epsilon = 0.001);
        assert_abs_diff_eq!(TET12::A440.hz(&Pitch::E4), 329.628, epsilon = 0.001);
        assert_abs_diff_eq!(TET12::A440.hz(&Pitch::F4), 349.228, epsilon = 0.001);
        assert_abs_diff_eq!(TET12::A440.hz(&Pitch::G4), 391.995, epsilon = 0.001);
        assert_abs_diff_eq!(TET12::A440.hz(&Pitch::B4), 493.883, epsilon = 0.001);

        assert_abs_diff_eq!(TET12::A440.hz(&Pitch::Gb4), 369.994, epsilon = 0.001);
        assert_abs_diff_eq!(TET12::A440.hz(&Pitch::Fs4), 369.994, epsilon = 0.001);
    }

    #[quickcheck]
    fn tet12_octave_up_doubles_hz_examples(pitch: Pitch) {
        assert_abs_diff_eq!(
            TET12::A440.hz(&pitch.octave_up()),
            TET12::A440.hz(&pitch) * 2.0,
            epsilon = 0.001
        );
    }

    #[quickcheck]
    fn tet12_octave_up_halves_hz(pitch: Pitch) {
        assert_abs_diff_eq!(
            TET12::A440.hz(&pitch.octave_down()),
            TET12::A440.hz(&pitch) / 2.0,
            epsilon = 0.001
        );
    }

    #[quickcheck]
    fn tet12_enharmonic_pitches_have_same_hz(a: Pitch, b: Pitch) {
        if a.enharmonic(&b) {
            assert_abs_diff_eq!(TET12::A440.hz(&a), TET12::A440.hz(&b), epsilon = 0.001);
        }
    }
}
