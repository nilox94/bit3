//! Pipeline specification: [`Pass`] / [`Phase`] types and the [`pipeline!`] macro.

/// One LLVM pass in a normalization phase.
pub struct Pass {
    pub name: &'static str,
    pub blurb: &'static str,
}

/// A named group of passes run in order before the next phase.
pub struct Phase {
    pub title: &'static str,
    pub passes: &'static [Pass],
}

/// Declare normalization phases; expands `PHASES` and `NORMALIZE_PASS_PIPELINE` at the call site.
#[macro_export]
macro_rules! pipeline {
    (
        $(
            phase $title:literal {
                $( $pass:literal $(=> $blurb:literal)? ),+ $(,)?
            }
        )+
    ) => {
        pub const PHASES: &[$crate::normalizer::pipeline_spec::Phase] = &[
            $( $crate::pipeline!(@phase $title { $( $pass $(=> $blurb)? ),+ } ), )+
        ];

        pub const NORMALIZE_PASS_PIPELINE: &str = $crate::macros::str_join!(
            ",",
            $( $crate::pipeline!(@phase_csv $( $pass ),+ ) ),+
        );
    };

    (@phase $title:literal { $( $pass:literal $(=> $blurb:literal)? ),+ }) => {
        $crate::normalizer::pipeline_spec::Phase {
            title: $title,
            passes: &[
                $( $crate::normalizer::pipeline_spec::Pass {
                    name: $pass,
                    blurb: $crate::pipeline!(@blurb $($blurb)?),
                }, )+
            ],
        }
    };

    (@blurb $b:literal) => { $b };
    (@blurb) => { "" };

    (@phase_csv $( $pass:literal ),+ $(,)?) => {
        $crate::macros::str_join!(",", $( $pass ),+)
    };
}
