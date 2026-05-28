//! Internal compile-time macros.

/// Join fragments with `$sep` at compile time via [`const_format::concatcp`].
macro_rules! str_join {
    ($sep:expr, $last:expr) => { $last };
    ($sep:expr, $head:expr, $($tail:expr),+ $(,)?) => {
        ::const_format::concatcp!($head, $sep, str_join!($sep, $($tail),+))
    };
}

pub(crate) use str_join;

#[cfg(test)]
mod tests {
    use super::str_join;

    #[test]
    fn str_join() {
        const SINGLE: &str = str_join!(",", "only");
        const PAIR: &str = str_join!(",", "a", "b",);
        const NESTED: &str = str_join!("_", r"¯\", str_join!("_", "(ツ)", "/¯"));

        assert_eq!(SINGLE, "only");
        assert_eq!(PAIR, "a,b");
        assert_eq!(NESTED, r"¯\_(ツ)_/¯");
    }
}
