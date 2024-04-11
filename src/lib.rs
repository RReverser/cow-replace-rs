// Disable no_std in doctests on stable Rust.
// See https://github.com/RReverser/cow-utils-rs/pull/1#issuecomment-586973518.
#![cfg_attr(any(not(doctest), feature = "nightly"), no_std)]
#![cfg_attr(feature = "nightly", feature(pattern))]

extern crate alloc as std;

use std::{
    borrow::{Cow, ToOwned},
    string::String,
};

/// This trait is a shim for the required functionality
/// normally provided directly by [`std::str::pattern::Pattern`]
/// (which is currently unstable).
///
/// On stable Rust it's implemented on the same standard types as
/// [`std::str::pattern::Pattern`], but on nightly you can enable
/// a `"nightly"` feature and any custom types implementing
/// [`std::str::pattern::Pattern`] will be supported as well.
pub trait Pattern<'s> {
    /// This will always be [`std::str::MatchIndices<'s,
    /// Self>`](std::str::MatchIndices) but we can't spell it out because it
    /// requires `Self: `[`std::str::pattern::Pattern`] and that trait bound is
    /// currently unstable and can't be written in a stable Rust.
    type MatchIndices: Iterator<Item = (usize, &'s str)>;

    /// A wrapper for [`&str::match_indices`] with a given pattern.
    fn match_indices_in(self, s: &'s str) -> Self::MatchIndices;
}

macro_rules! impl_pattern {
    ($ty:ty $(where $($bound:tt)*)?) => {
        impl<'s $(, $($bound)*)?> Pattern<'s> for $ty {
            type MatchIndices = std::str::MatchIndices<'s, Self>;

            fn match_indices_in(self, s: &'s str) -> Self::MatchIndices {
                s.match_indices(self)
            }
        }
    };
}

#[cfg(not(feature = "nightly"))]
const _: () = {
    impl_pattern!(char);
    impl_pattern!(&str);
    impl_pattern!(&String);
    impl_pattern!(&[char]);
    impl_pattern!(&&str);
    impl_pattern!(F where F: FnMut(char) -> bool);
};

#[cfg(feature = "nightly")]
impl_pattern!(P where P: std::str::pattern::Pattern<'s>);

/// Some [`str`] methods perform destructive transformations and so
/// return [`String`] even when no modification is necessary.
///
/// This helper trait provides drop-in variants of such methods, but
/// instead avoids allocations when no modification is necessary.
///
/// For now only implemented for [`&str`](str) and returns
/// [`Cow<str>`](std::borrow::Cow), but in the future might be extended
/// to other types.
pub trait CowUtils<'s> {
    type Output;

    /// Replaces all matches of a pattern with another string.
    fn cow_replace(self, pattern: impl Pattern<'s>, to: &str) -> Self::Output;
    /// Replaces first N matches of a pattern with another string.
    fn cow_replacen(self, from: impl Pattern<'s>, to: &str, count: usize) -> Self::Output;
    /// Returns a copy of this string where each character is mapped to its
    /// ASCII lower case equivalent.
    fn cow_to_ascii_lowercase(self) -> Self::Output;
    /// Returns the lowercase equivalent of this string slice.
    fn cow_to_lowercase(self) -> Self::Output;
    /// Returns a copy of this string where each character is mapped to its
    /// ASCII upper case equivalent.
    fn cow_to_ascii_uppercase(self) -> Self::Output;
    /// Returns the uppercase equivalent of this string slice.
    fn cow_to_uppercase(self) -> Self::Output;
}

unsafe fn cow_replace<'s>(
    src: &'s str,
    match_indices: impl Iterator<Item = (usize, &'s str)>,
    to: &str,
) -> Cow<'s, str> {
    let mut result = Cow::default();
    let mut last_start = 0;
    for (index, matched) in match_indices {
        result += src.get_unchecked(last_start..index);
        if !to.is_empty() {
            result.to_mut().push_str(to);
        }
        last_start = index + matched.len();
    }
    result += src.get_unchecked(last_start..);
    result
}

impl<'s> CowUtils<'s> for &'s str {
    type Output = Cow<'s, str>;

    /// This is similar to [`str::replace`](https://doc.rust-lang.org/std/primitive.str.html#method.replace), but returns
    /// a slice of the original string when possible:
    /// ```
    /// # use cow_utils::CowUtils;
    /// # use assert_matches::assert_matches;
    /// # use std::borrow::Cow;
    /// assert_matches!("abc".cow_replace("def", "ghi"), Cow::Borrowed("abc"));
    /// assert_matches!("$$str$$".cow_replace("$", ""), Cow::Borrowed("str"));
    /// assert_matches!("aaaaa".cow_replace("a", ""), Cow::Borrowed(""));
    /// assert_matches!("abc".cow_replace("b", "d"), Cow::Owned(s) if s == "adc");
    /// assert_matches!("$a$b$".cow_replace("$", ""), Cow::Owned(s) if s == "ab");
    /// ```
    fn cow_replace(self, pattern: impl Pattern<'s>, to: &str) -> Self::Output {
        unsafe { cow_replace(self, pattern.match_indices_in(self), to) }
    }

    /// This is similar to [`str::replacen`](https://doc.rust-lang.org/std/primitive.str.html#method.replacen), but returns
    /// a slice of the original string when possible:
    /// ```
    /// # use cow_utils::CowUtils;
    /// # use assert_matches::assert_matches;
    /// # use std::borrow::Cow;
    /// assert_matches!("abc".cow_replacen("def", "ghi", 10), Cow::Borrowed("abc"));
    /// assert_matches!("$$str$$".cow_replacen("$", "", 2), Cow::Borrowed("str$$"));
    /// assert_matches!("$a$b$".cow_replacen("$", "", 1), Cow::Borrowed("a$b$"));
    /// assert_matches!("aaaaa".cow_replacen("a", "", 10), Cow::Borrowed(""));
    /// assert_matches!("aaaaa".cow_replacen("a", "b", 0), Cow::Borrowed("aaaaa"));
    /// assert_matches!("abc".cow_replacen("b", "d", 1), Cow::Owned(s) if s == "adc");
    /// ```
    fn cow_replacen(self, pattern: impl Pattern<'s>, to: &str, count: usize) -> Self::Output {
        unsafe { cow_replace(self, pattern.match_indices_in(self).take(count), to) }
    }

    /// This is similar to [`str::to_ascii_lowercase`](https://doc.rust-lang.org/std/primitive.str.html#method.to_ascii_lowercase), but returns
    /// original slice when possible:
    /// ```
    /// # use cow_utils::CowUtils;
    /// # use assert_matches::assert_matches;
    /// # use std::borrow::Cow;
    /// assert_matches!("abcd123".cow_to_ascii_lowercase(), Cow::Borrowed("abcd123"));
    /// assert_matches!("ὀδυσσεύς".cow_to_ascii_lowercase(), Cow::Borrowed("ὀδυσσεύς"));
    /// assert_matches!("ὈΔΥΣΣΕΎΣ".cow_to_ascii_lowercase(), Cow::Borrowed("ὈΔΥΣΣΕΎΣ"));
    /// assert_matches!("AbCd".cow_to_ascii_lowercase(), Cow::Owned(s) if s == "abcd");
    /// ```
    fn cow_to_ascii_lowercase(self) -> Self::Output {
        match self.as_bytes().iter().position(u8::is_ascii_uppercase) {
            Some(pos) => {
                let mut output = self.to_owned();
                // We already know position of the first uppercase char,
                // so no need to rescan the part before it.
                unsafe { output.get_unchecked_mut(pos..) }.make_ascii_lowercase();
                Cow::Owned(output)
            }
            None => Cow::Borrowed(self),
        }
    }

    /// This is similar to [`str::to_lowercase`](https://doc.rust-lang.org/std/primitive.str.html#method.to_lowercase), but returns
    /// original slice when possible:
    /// ```
    /// # use cow_utils::CowUtils;
    /// # use assert_matches::assert_matches;
    /// # use std::borrow::Cow;
    /// assert_matches!("abcd123".cow_to_lowercase(), Cow::Borrowed("abcd123"));
    /// assert_matches!("ὀδυσσεύς".cow_to_lowercase(), Cow::Borrowed("ὀδυσσεύς"));
    /// assert_matches!("ὈΔΥΣΣΕΎΣ".cow_to_lowercase(), Cow::Owned(s) if s == "ὀδυσσεύς");
    /// assert_matches!("AbCd".cow_to_lowercase(), Cow::Owned(s) if s == "abcd");
    /// assert_matches!("ᾈ".cow_to_lowercase(), Cow::Owned(s) if s == "ᾀ");
    /// ```
    fn cow_to_lowercase(self) -> Self::Output {
        // `str::to_lowercase` has a tricky edgecase with handling of Σ.
        // We could optimise this by duplicating some code from stdlib,
        // but it wouldn't be particularly clean, so for now just check
        // if the string contains any uppercase char and let
        // `str::to_lowercase` rescan it again.
        if self.chars().any(changes_when_lowercased) {
            Cow::Owned(self.to_lowercase())
        } else {
            Cow::Borrowed(self)
        }
    }

    /// This is similar to [`str::to_ascii_uppercase`](https://doc.rust-lang.org/std/primitive.str.html#method.to_ascii_uppercase), but returns
    /// original slice when possible:
    /// ```
    /// # use cow_utils::CowUtils;
    /// # use assert_matches::assert_matches;
    /// # use std::borrow::Cow;
    /// assert_matches!("ABCD123".cow_to_ascii_uppercase(), Cow::Borrowed("ABCD123"));
    /// assert_matches!("ὈΔΥΣΣΕΎΣ".cow_to_ascii_uppercase(), Cow::Borrowed("ὈΔΥΣΣΕΎΣ"));
    /// assert_matches!("ὀδυσσεύς".cow_to_ascii_uppercase(), Cow::Borrowed("ὀδυσσεύς"));
    /// assert_matches!("AbCd".cow_to_ascii_uppercase(), Cow::Owned(s) if s == "ABCD");
    /// ```
    fn cow_to_ascii_uppercase(self) -> Self::Output {
        match self.as_bytes().iter().position(u8::is_ascii_lowercase) {
            Some(pos) => {
                let mut output = self.to_owned();
                // We already know position of the first lowercase char,
                // so no need to rescan the part before it.
                unsafe { output.get_unchecked_mut(pos..) }.make_ascii_uppercase();
                Cow::Owned(output)
            }
            None => Cow::Borrowed(self),
        }
    }

    /// This is similar to [`str::to_uppercase`](https://doc.rust-lang.org/std/primitive.str.html#method.to_uppercase), but returns
    /// original slice when possible:
    /// ```
    /// # use cow_utils::CowUtils;
    /// # use assert_matches::assert_matches;
    /// # use std::borrow::Cow;
    /// assert_matches!("ABCD123".cow_to_uppercase(), Cow::Borrowed("ABCD123"));
    /// assert_matches!("ὈΔΥΣΣΕΎΣ".cow_to_uppercase(), Cow::Borrowed("ὈΔΥΣΣΕΎΣ"));
    /// assert_matches!("ὀδυσσεύς".cow_to_uppercase(), Cow::Owned(s) if s == "ὈΔΥΣΣΕΎΣ");
    /// assert_matches!("AbCd".cow_to_uppercase(), Cow::Owned(s) if s == "ABCD");
    /// assert_matches!("ᾈ".cow_to_uppercase(), Cow::Owned(s) if s == "ἈΙ");
    /// ```
    fn cow_to_uppercase(self) -> Self::Output {
        match self.find(changes_when_uppercased) {
            Some(pos) => {
                let mut output = String::with_capacity(self.len());
                // We already know position of the first lowercase char,
                // so no need to rescan the part before it - just copy it.
                output.push_str(unsafe { self.get_unchecked(..pos) });
                output.extend(
                    unsafe { self.get_unchecked(pos..) }
                        .chars()
                        .flat_map(char::to_uppercase),
                );
                Cow::Owned(output)
            }
            None => Cow::Borrowed(self),
        }
    }
}

fn changes_when_lowercased(c: char) -> bool {
    !core::iter::once(c).eq(c.to_lowercase())
}

fn changes_when_uppercased(c: char) -> bool {
    !core::iter::once(c).eq(c.to_uppercase())
}
