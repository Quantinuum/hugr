//! Dump standard extensions in serialized form.
use anyhow::Result;
use clap::Parser;
use hugr::Extension;
use hugr::extension::ExtensionRegistry;
use std::{io::Write, path::PathBuf};

/// Dump the standard extensions.
#[derive(Parser, Debug)]
#[clap(version = "1.0", long_about = None)]
#[clap(about = "Write standard extensions.")]
#[group(id = "hugr")]
#[non_exhaustive]
pub struct ExtArgs {
    /// Output directory
    #[arg(
        default_value = ".",
        short,
        long,
        value_name = "OUTPUT",
        help = "Output directory."
    )]
    pub outdir: PathBuf,
    /// Add the extension version to the output filename, e.g. "foo-1.2.3.json".
    #[arg(
        long,
        help = "Add the extension version to the output filename.",
        default_value_t = false
    )]
    pub versioned: bool,
}

impl ExtArgs {
    /// Write out the standard extensions in serialized form.
    ///
    /// Qualified names of extensions used to generate directories under the specified output directory.
    /// The extension version is added to the json filename.
    ///
    /// E.g. extension "foo.bar.baz" will be written to "OUTPUT/foo/bar/baz-1.2.3.json".
    pub fn run_dump(&self, registry: &ExtensionRegistry) -> Result<()> {
        if self.versioned {
            registry
                .iter_all()
                .try_for_each(|ext| self.dump_extension(ext))?;
        } else {
            // The STD registry should only contain one version of each
            // extension, so we can just take the latest version for each
            // extension name and avoid overriding files.
            registry
                .iter()
                .map(|ext| ext.latest())
                .try_for_each(|ext| self.dump_extension(ext))?;
        }

        Ok(())
    }

    fn dump_extension(&self, ext: &Extension) -> Result<()> {
        let mut path = self.outdir.clone();
        let mut parts = ext.name().split('.').peekable();
        while let Some(part) = parts.next() {
            if parts.peek().is_some() {
                path.push(part);
                continue;
            }

            // Optionally add the extension version to the output filename, e.g. "foo-1.2.3.json".
            if self.versioned {
                path.push(format!("{part}-{}.json", ext.version()));
            } else {
                path.push(format!("{part}.json"));
            }
        }

        std::fs::create_dir_all(path.clone().parent().unwrap())?;
        // file buffer
        let mut file = std::fs::File::create(&path)?;

        serde_json::to_writer_pretty(&mut file, &ext)?;

        // write newline, for pre-commit end of file check that edits the file to
        // add newlines if missing.
        file.write_all(b"\n")?;

        Ok(())
    }
}
