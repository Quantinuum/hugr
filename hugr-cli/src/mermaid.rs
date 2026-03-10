//! Render mermaid diagrams.
use std::io::{Read, Write};

use crate::CliError;
use crate::hugr_io::HugrInputArgs;
use anyhow::Result;
use clap::Parser;
use clio::Output;
use hugr::HugrView;
use hugr::hugr::views::render::NodeLabel;
use hugr::package::PackageValidationError;

/// Dump the standard extensions.
#[derive(Parser, Debug)]
#[clap(version = "1.0", long_about = None)]
#[clap(about = "Render mermaid diagrams..")]
#[group(id = "hugr")]
#[non_exhaustive]
pub struct MermaidArgs {
    /// Hugr input.
    #[command(flatten)]
    pub input_args: HugrInputArgs,

    /// Validate package.
    #[arg(
        long,
        help = "Validate before rendering, includes extension inference."
    )]
    pub validate: bool,

    /// Print debug metadata.
    #[arg(
        short = 'D',
        long,
        help = "Print debug info attached to nodes if it exists."
    )]
    pub debug_info: bool,

    /// Output file '-' for stdout
    #[clap(long, short, value_parser, default_value = "-")]
    output: Output,
}

impl MermaidArgs {
    /// Write the mermaid diagram to the output with optional input/output overrides.
    ///
    /// # Arguments
    ///
    /// * `input_override` - Optional reader to use instead of the CLI input argument.
    /// * `output_override` - Optional writer to use instead of the CLI output argument.
    pub fn run_print_with_io<R: Read, W: Write>(
        &mut self,
        input_override: Option<R>,
        output_override: Option<W>,
    ) -> Result<()> {
        self.run_print_envelope_with_io(input_override, output_override)
    }

    /// Write the mermaid diagram for a HUGR envelope with optional I/O overrides.
    fn run_print_envelope_with_io<R: Read, W: Write>(
        &mut self,
        input_override: Option<R>,
        mut output_override: Option<W>,
    ) -> Result<()> {
        let (desc, package) = self
            .input_args
            .get_described_package_with_reader(input_override)?;

        let generator = desc.generator();
        if self.validate {
            package
                .validate()
                .map_err(|val_err| CliError::validation(generator, val_err))?;
        }

        for hugr in package.modules {
            let mmd_fmt = if self.debug_info {
                // TODO: hardcoded
                hugr.mermaid_format()
                    .with_node_labels(NodeLabel::MetadataKey("core.debug_info".to_string()))
            } else {
                hugr.mermaid_format()
            };

            if let Some(ref mut writer) = output_override {
                writeln!(writer, "{}", mmd_fmt.finish())?;
            } else {
                writeln!(self.output, "{}", mmd_fmt.finish())?;
            }
        }
        Ok(())
    }

    /// Write the mermaid diagram for a legacy HUGR json with optional I/O overrides.
    #[expect(deprecated)]
    fn run_print_hugr_with_io<R: Read, W: Write>(
        &mut self,
        input_override: Option<R>,
        mut output_override: Option<W>,
    ) -> Result<()> {
        let hugr = self.input_args.get_hugr_with_reader(input_override)?;

        if self.validate {
            hugr.validate()
                .map_err(PackageValidationError::Validation)?;
        }

        if let Some(ref mut writer) = output_override {
            writeln!(writer, "{}", hugr.mermaid_string())?;
        } else {
            writeln!(self.output, "{}", hugr.mermaid_string())?;
        }
        Ok(())
    }

    /// Write the mermaid diagram to the output.
    pub fn run_print(&mut self) -> Result<()> {
        self.run_print_with_io(None::<&[u8]>, None::<Vec<u8>>)
    }

    /// Write the mermaid diagram for a HUGR envelope.
    pub fn run_print_envelope(&mut self) -> Result<()> {
        self.run_print_envelope_with_io(None::<&[u8]>, None::<Vec<u8>>)
    }

    /// Write the mermaid diagram for a legacy HUGR json.
    #[deprecated(since = "0.27.0")]
    pub fn run_print_hugr(&mut self) -> Result<()> {
        self.run_print_hugr_with_io(None::<&[u8]>, None::<Vec<u8>>)
    }
}
