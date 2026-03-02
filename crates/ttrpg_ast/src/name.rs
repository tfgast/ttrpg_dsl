use std::borrow::Borrow;
use std::fmt;
use std::ops::Deref;
use std::sync::Arc;

/// Newtype wrapper for identifier strings (type names, field names, variable names, etc.).
///
/// Backed by `Arc<str>` so that `clone()` is a cheap reference-count bump
/// rather than a heap allocation.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name(Arc<str>);

impl Name {
    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn into_inner(self) -> String {
        // We can't move out of an Arc, so we have to copy.
        self.0.to_string()
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl From<String> for Name {
    fn from(s: String) -> Self {
        Name(Arc::from(s))
    }
}

impl From<&str> for Name {
    fn from(s: &str) -> Self {
        Name(Arc::from(s))
    }
}

impl From<Arc<str>> for Name {
    fn from(s: Arc<str>) -> Self {
        Name(s)
    }
}

impl AsRef<str> for Name {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

impl Borrow<str> for Name {
    fn borrow(&self) -> &str {
        &self.0
    }
}

impl Deref for Name {
    type Target = str;

    fn deref(&self) -> &str {
        &self.0
    }
}

impl PartialEq<str> for Name {
    fn eq(&self, other: &str) -> bool {
        &*self.0 == other
    }
}

impl PartialEq<&str> for Name {
    fn eq(&self, other: &&str) -> bool {
        &*self.0 == *other
    }
}

impl PartialEq<Name> for str {
    fn eq(&self, other: &Name) -> bool {
        self == &*other.0
    }
}

impl PartialEq<Name> for &str {
    fn eq(&self, other: &Name) -> bool {
        *self == &*other.0
    }
}

#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for Name {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let s: String = u.arbitrary()?;
        Ok(Name::from(s))
    }
}
