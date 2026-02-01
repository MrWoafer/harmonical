pub trait Enharmonic {
    fn enharmonic(&self, other: &Self) -> bool;
}

#[macro_export]
macro_rules! assert_enharmonic {
    ($left:expr, $right:expr $(,)?) => {
        assert_enharmonic!($left, $right, "")
    };
    ($left:expr, $right:expr, $($extra:tt)+) => {
        assert!(
            $crate::enharmonic::Enharmonic::enharmonic(&$left, &$right),
            "{}",
            format!(
                "assertion `left.enharmonic(&right)` failed: {}\n  left: {}\n right: {}",
                format!($($extra)*),
                $left,
                $right
            )
        )
    };
}

pub use assert_enharmonic;

#[macro_export]
macro_rules! assert_not_enharmonic {
    ($left:expr, $right:expr $(,)?) => {
        assert_not_enharmonic!($left, $right, "")
    };
    ($left:expr, $right:expr, $($extra:tt)+) => {
        assert!(
            !$crate::enharmonic::Enharmonic::enharmonic(&$left, &$right),
            "{}",
            format!(
                "assertion `!left.enharmonic(&right)` failed: {}\n  left: {}\n right: {}",
                format!($($extra)*),
                $left,
                $right
            )
        )
    };
}

pub use assert_not_enharmonic;

#[cfg(test)]
mod tests {
    use crate::pitches::PitchClass;

    #[test]
    fn assert_enharmonic_pass() {
        assert_enharmonic!(PitchClass::Ab, PitchClass::Gs);
    }

    #[test]
    #[should_panic = r#"assertion `left.enharmonic(&right)` failed: 
  left: Ab
 right: B"#]
    fn assert_enharmonic_fail_no_msg() {
        assert_enharmonic!(PitchClass::Ab, PitchClass::B);
    }

    #[test]
    #[should_panic = r#"assertion `left.enharmonic(&right)` failed: aw, nuts! 14 23
  left: Ab
 right: B"#]
    fn assert_enharmonic_fail_with_msg() {
        let x = 14;
        let y = 23;
        assert_enharmonic!(PitchClass::Ab, PitchClass::B, "aw, nuts! {x} {}", y);
    }

    #[test]
    fn assert_not_enharmonic_pass() {
        assert_not_enharmonic!(PitchClass::D, PitchClass::C);
    }

    #[test]
    #[should_panic = r#"assertion `!left.enharmonic(&right)` failed: 
  left: C#
 right: Db"#]
    fn assert_not_enharmonic_fail_no_msg() {
        assert_not_enharmonic!(PitchClass::Cs, PitchClass::Db);
    }

    #[test]
    #[should_panic = r#"assertion `!left.enharmonic(&right)` failed: aw, nuts! 14 23
  left: C#
 right: Db"#]
    fn assert_not_enharmonic_fail_with_msg() {
        let x = 14;
        let y = 23;
        assert_not_enharmonic!(PitchClass::Cs, PitchClass::Db, "aw, nuts! {x} {}", y);
    }
}
