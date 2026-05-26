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

/// Retained versions for one extension id.
///
/// Contains a set of versions for a given extension, and the corresponding [Weak]
/// references to each [Extension].
///
/// The registry keeps at most one extension per semver-compatible group: when a
/// newer compatible version is registered, it replaces the older compatible
/// definition. Incompatible versions are retained side by side so older HUGRs can
/// still resolve against the appropriate definition.
#[derive(Debug, Clone)]
pub struct WeakExtensionVersions {
    id: ExtensionId,
    versions: BTreeMap<Version, Weak<Extension>>,
}

impl WeakExtensionVersions {
    /// Create a new `WeakExtensionVersions` with a single entry.
    fn new(id: ExtensionId, version: Version, ext: Weak<Extension>) -> Self {
        Self {
            id,
            versions: [(version, ext)].into(),
        }
    }

    /// Returns the highest version extension registered for this id.
    #[must_use]
    fn latest(&self) -> (&Version, &Weak<Extension>) {
        self.versions
            .last_key_value()
            .expect("WeakExtensionVersions always contains at least one extension")
    }

    /// Return the highest retained extension compatible with `requested`, if any.
    #[must_use]
    fn get_compatible(&self, requested: &Version) -> Option<(&Version, &Weak<Extension>)> {
        let (version, extension) = self.versions.range(requested..).next()?;
        semver_compatible(version, requested).then_some((version, extension))
    }

    /// Gets the extension satisfying an optional serialized version requirement.
    ///
    /// If `requested` is `Some(version)`, returns the highest retained
    /// extension compatible with `version`. If `requested` is `None`, returns
    /// the latest retained extension.
    ///
    /// This is used when deserializing older HUGRs that may not have a version
    /// specified for their extensions.
    #[must_use]
    fn get_req(&self, requested: Option<&Version>) -> Option<(&Version, &Weak<Extension>)> {
        match requested {
            Some(version) => self.get_compatible(version),
            None => Some(self.latest()),
        }
    }

    /// Register a new extension in the versions for this id.
    ///
    /// Returns `true` if the extension was added.
    /// Returns `false` if the same version, or a later compatible one was already present.
    fn register(&mut self, version: Version, ext: Weak<Extension>) -> bool {
        #[cfg(debug_assertions)]
        {
            let extension = ext
                .upgrade()
                .expect("weak extension ARC must be upgradeable when registered");
            assert_eq!(
                extension.name(),
                &self.id,
                "extension id does not match WeakExtensionVersions id"
            );
            drop(extension);
        }

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

    /// Returns a registered version that is in the same semver-compatibility group as the requested version, if any.
    ///
    /// The registry keeps at most one extension per semver-compatible group: when a
    /// newer compatible version is registered, it replaces the older compatible
    /// definition. Incompatible versions are retained side by side so older HUGRs can
    /// still resolve against the appropriate definition.
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

    /// Iterate over the weak references in the registry and their versions.
    fn iter(&self) -> impl Iterator<Item = (&Version, &Weak<Extension>)> {
        self.versions.iter()
    }

    /// Returns an iterator over the weak references in the registry and their versions.
    fn into_iter(self) -> impl Iterator<Item = (Version, Weak<Extension>)> {
        self.versions.into_iter()
    }
}

impl WeakExtensionRegistry {
    /// Create a new weak registry from a list of extensions and their ids.
    pub fn new(
        extensions: impl IntoIterator<Item = (ExtensionId, Version, Weak<Extension>)>,
    ) -> Self {
        let mut res = Self::default();
        for (id, version, ext) in extensions {
            res.register(id, version, ext);
        }
        res
    }

    /// Gets the Extension with the given name
    #[must_use]
    pub fn get_latest(&self, name: &str) -> Option<(&Version, &Weak<Extension>)> {
        self.exts.get(name).map(WeakExtensionVersions::latest)
    }

    /// Gets the Extension satisfying an optional serialized version
    /// requirement.
    ///
    /// If found a matching extension, returns a Weak reference to it along with
    /// its version. If no matching extension is found, returns None.
    #[must_use]
    pub fn get_req(
        &self,
        name: &str,
        version: Option<&Version>,
    ) -> Option<(&Version, &Weak<Extension>)> {
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
    pub fn register(
        &mut self,
        id: ExtensionId,
        version: Version,
        ext: impl Into<Weak<Extension>>,
    ) -> bool {
        let ext = ext.into();
        match self.exts.entry(id.clone()) {
            std::collections::btree_map::Entry::Occupied(mut occupied) => {
                occupied.get_mut().register(version, ext)
            }
            std::collections::btree_map::Entry::Vacant(vacant) => {
                vacant.insert(WeakExtensionVersions::new(id, version, ext));
                true
            }
        }
    }

    /// Returns an iterator over the weak references in the registry and their ids.
    pub fn iter(&self) -> impl Iterator<Item = (&ExtensionId, &Version, &Weak<Extension>)> {
        self.exts.iter().map(|(id, versions)| {
            let (version, ext) = versions.latest();
            (id, version, ext)
        })
    }

    /// Returns an iterator over all retained weak references and their ids.
    pub fn iter_all(&self) -> impl Iterator<Item = (&ExtensionId, &Version, &Weak<Extension>)> {
        self.exts.iter().flat_map(|(id, versions)| {
            versions
                .iter()
                .map(move |(version, ext)| (id, version, ext))
        })
    }

    /// Returns an iterator over the weak references in the registry.
    pub fn extensions(&self) -> impl Iterator<Item = (&Version, &Weak<Extension>)> {
        self.exts.values().map(WeakExtensionVersions::latest)
    }

    /// Returns an iterator over all retained weak references, including their id and version.
    pub fn all_extensions(
        &self,
    ) -> impl Iterator<Item = (&ExtensionId, &Version, &Weak<Extension>)> {
        self.exts.values().flat_map(|versions| {
            versions
                .iter()
                .map(move |(version, ext)| (&versions.id, version, ext))
        })
    }

    /// Returns an iterator over the extension ids in the registry.
    pub fn ids(&self) -> impl Iterator<Item = &ExtensionId> {
        self.exts.keys()
    }
}

impl IntoIterator for WeakExtensionRegistry {
    type Item = (ExtensionId, Version, Weak<Extension>);
    type IntoIter = std::vec::IntoIter<(ExtensionId, Version, Weak<Extension>)>;

    fn into_iter(self) -> Self::IntoIter {
        self.exts
            .into_iter()
            .flat_map(|(id, ext_versions)| {
                ext_versions
                    .into_iter()
                    .map(move |(version, ext)| (id.clone(), version, ext))
            })
            .collect_vec()
            .into_iter()
    }
}

impl<'a> TryFrom<&'a WeakExtensionRegistry> for ExtensionRegistry {
    type Error = ();

    fn try_from(weak: &'a WeakExtensionRegistry) -> Result<Self, Self::Error> {
        let exts: Vec<Arc<Extension>> = weak
            .all_extensions()
            .map(|(_, _, w)| w.upgrade().ok_or(()))
            .try_collect()?;
        Ok(ExtensionRegistry::new(exts))
    }
}

impl TryFrom<WeakExtensionRegistry> for ExtensionRegistry {
    type Error = ();

    fn try_from(weak: WeakExtensionRegistry) -> Result<Self, Self::Error> {
        let exts: Vec<Arc<Extension>> = weak
            .into_iter()
            .map(|(_, _, w)| w.upgrade().ok_or(()))
            .try_collect()?;
        Ok(ExtensionRegistry::new(exts))
    }
}

impl<'a> From<&'a ExtensionRegistry> for WeakExtensionRegistry {
    fn from(reg: &'a ExtensionRegistry) -> Self {
        Self::new(reg.iter_all().map(|ext| {
            (
                ext.name().clone(),
                ext.version().clone(),
                Arc::downgrade(ext),
            )
        }))
    }
}
