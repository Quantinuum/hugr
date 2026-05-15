use std::collections::BTreeMap;
use std::sync::{Arc, Weak};

use itertools::Itertools;

use derive_more::Display;

use crate::Extension;
use crate::extension::{ExtensionId, ExtensionRegistry, Version, semver_compatible};

/// The equivalent to an [`ExtensionRegistry`] that only contains weak
/// references.
///
/// This is used to resolve extensions pointers while the extensions themselves
/// (and the [`Arc`] that contains them) are being initialized.
#[derive(Debug, Display, Default, Clone)]
#[display("WeakExtensionRegistry[{}]", exts.keys().join(", "))]
pub struct WeakExtensionRegistry {
    /// The extensions in the registry.
    exts: BTreeMap<ExtensionId, WeakExtensionVersions>,
}

/// Weak references retained for one extension id.
#[derive(Debug, Clone)]
pub struct WeakExtensionVersions {
    id: ExtensionId,
    versions: BTreeMap<Version, Weak<Extension>>,
}

impl WeakExtensionVersions {
    fn new(id: ExtensionId, ext: Weak<Extension>) -> Self {
        let version = ext
            .upgrade()
            .expect("weak extension must be upgradeable when registered")
            .version()
            .clone();
        Self {
            id,
            versions: [(version, ext)].into(),
        }
    }

    fn latest(&self) -> &Weak<Extension> {
        self.versions
            .last_key_value()
            .expect("WeakExtensionVersions always contains at least one extension")
            .1
    }

    fn compatible(&self, requested: &Version) -> Option<&Weak<Extension>> {
        let (version, extension) = self.versions.range(requested..).next()?;
        semver_compatible(version, requested).then_some(extension)
    }

    fn get_req(&self, requested: Option<&Version>) -> Option<&Weak<Extension>> {
        requested
            .and_then(|version| self.compatible(version))
            .or_else(|| requested.is_none().then(|| self.latest()))
    }

    fn register(&mut self, ext: Weak<Extension>) -> bool {
        let extension = ext
            .upgrade()
            .expect("weak extension must be upgradeable when registered");
        assert_eq!(
            extension.name(),
            &self.id,
            "extension id does not match WeakExtensionVersions id"
        );
        let version = extension.version().clone();
        drop(extension);

        let compatible_version = self.compatible_registered_version(&version);

        let Some(compatible_version) = compatible_version else {
            self.versions.insert(version, ext);
            return true;
        };
        if compatible_version > version {
            return false;
        }

        self.versions.remove(&compatible_version);
        self.versions.insert(version, ext);
        true
    }

    fn compatible_registered_version(&self, version: &Version) -> Option<Version> {
        if let Some((candidate, _)) = self.versions.range(..=version).next_back()
            && semver_compatible(version, candidate)
        {
            return Some(candidate.clone());
        }
        self.versions
            .range(version..)
            .next()
            .filter(|(candidate, _)| semver_compatible(candidate, version))
            .map(|(candidate, _)| candidate.clone())
    }

    fn iter(&self) -> impl Iterator<Item = &Weak<Extension>> {
        self.versions.values()
    }

    fn into_all(self) -> impl Iterator<Item = Weak<Extension>> {
        self.versions.into_values()
    }
}

impl WeakExtensionRegistry {
    /// Create a new weak registry from a list of extensions and their ids.
    pub fn new(extensions: impl IntoIterator<Item = (ExtensionId, Weak<Extension>)>) -> Self {
        let mut res = Self::default();
        for (id, ext) in extensions {
            res.register(id, ext);
        }
        res
    }

    /// Gets the Extension with the given name
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&Weak<Extension>> {
        self.exts.get(name).map(WeakExtensionVersions::latest)
    }

    /// Gets the Extension satisfying an optional serialized version requirement.
    #[must_use]
    pub fn get_req(&self, name: &str, version: Option<&Version>) -> Option<&Weak<Extension>> {
        self.exts.get(name).and_then(|ext| ext.get_req(version))
    }

    /// Returns `true` if the registry contains an extension with the given name.
    #[must_use]
    pub fn contains(&self, name: &str) -> bool {
        self.exts.contains_key(name)
    }

    /// Register a new extension in the registry.
    ///
    /// Returns `true` if the extension was added, `false` if it was already present.
    pub fn register(&mut self, id: ExtensionId, ext: impl Into<Weak<Extension>>) -> bool {
        let ext = ext.into();
        match self.exts.entry(id.clone()) {
            std::collections::btree_map::Entry::Occupied(mut occupied) => {
                occupied.get_mut().register(ext)
            }
            std::collections::btree_map::Entry::Vacant(vacant) => {
                vacant.insert(WeakExtensionVersions::new(id, ext));
                true
            }
        }
    }

    /// Returns an iterator over the weak references in the registry and their ids.
    pub fn iter(&self) -> impl Iterator<Item = (&ExtensionId, &Weak<Extension>)> {
        self.exts
            .iter()
            .map(|(id, versions)| (id, versions.latest()))
    }

    /// Returns an iterator over all retained weak references and their ids.
    pub fn iter_all(&self) -> impl Iterator<Item = (&ExtensionId, &Weak<Extension>)> {
        self.exts
            .iter()
            .flat_map(|(id, versions)| versions.iter().map(move |ext| (id, ext)))
    }

    /// Returns an iterator over the weak references in the registry.
    pub fn extensions(&self) -> impl Iterator<Item = &Weak<Extension>> {
        self.exts.values().map(WeakExtensionVersions::latest)
    }

    /// Returns an iterator over all retained weak references.
    pub fn all_extensions(&self) -> impl Iterator<Item = &Weak<Extension>> {
        self.exts.values().flat_map(WeakExtensionVersions::iter)
    }

    /// Returns an iterator over the extension ids in the registry.
    pub fn ids(&self) -> impl Iterator<Item = &ExtensionId> {
        self.exts.keys()
    }
}

impl IntoIterator for WeakExtensionRegistry {
    type Item = Weak<Extension>;
    type IntoIter = std::vec::IntoIter<Weak<Extension>>;

    fn into_iter(self) -> Self::IntoIter {
        self.exts
            .into_values()
            .flat_map(WeakExtensionVersions::into_all)
            .collect_vec()
            .into_iter()
    }
}

impl<'a> TryFrom<&'a WeakExtensionRegistry> for ExtensionRegistry {
    type Error = ();

    fn try_from(weak: &'a WeakExtensionRegistry) -> Result<Self, Self::Error> {
        let exts: Vec<Arc<Extension>> = weak
            .all_extensions()
            .map(|w| w.upgrade().ok_or(()))
            .try_collect()?;
        Ok(ExtensionRegistry::new(exts))
    }
}

impl TryFrom<WeakExtensionRegistry> for ExtensionRegistry {
    type Error = ();

    fn try_from(weak: WeakExtensionRegistry) -> Result<Self, Self::Error> {
        let exts: Vec<Arc<Extension>> = weak
            .into_iter()
            .map(|w| w.upgrade().ok_or(()))
            .try_collect()?;
        Ok(ExtensionRegistry::new(exts))
    }
}

impl<'a> From<&'a ExtensionRegistry> for WeakExtensionRegistry {
    fn from(reg: &'a ExtensionRegistry) -> Self {
        Self::new(
            reg.iter_all()
                .map(|ext| (ext.name().clone(), Arc::downgrade(ext))),
        )
    }
}
