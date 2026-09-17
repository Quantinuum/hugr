//! Helper methods to compute the node/edge/port style when rendering a HUGR
//! into dot or mermaid format.

use itertools::Itertools;
use std::collections::HashMap;

use portgraph::render::{EdgeStyle, NodeStyle, PortStyle, PresentationStyle};
use portgraph::{LinkView, MultiPortGraph, NodeIndex, PortIndex, PortView};

use crate::core::HugrNode;
use crate::hugr::internal::HugrInternals;
use crate::ops::OpTrait;
use crate::types::EdgeKind;
use crate::{Hugr, HugrView, Node};

/// Configuration for rendering an operation as a string.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RenderStringConfig {
    /// Include the version of the extension defining the operation.
    extension_version: bool,
    /// Include the operation's type arguments.
    print_type_args: bool,
    /// Qualify operation name with their extension identifier.
    qualify_name: bool,
}

impl RenderStringConfig {
    /// Create a configuration with qualified names and without versions or type arguments.
    pub const fn new() -> Self {
        Self {
            extension_version: false,
            print_type_args: false,
            qualify_name: true,
        }
    }

    /// Whether to include the extension version in the rendered output.
    pub fn extension_version(&self) -> bool {
        self.extension_version
    }

    /// Whether to print type arguments in the rendered output.
    pub fn print_type_args(&self) -> bool {
        self.print_type_args
    }

    /// Whether to qualify operation name with their extension identifier.
    pub fn qualify_name(&self) -> bool {
        self.qualify_name
    }

    /// Set whether to qualify operation name with their extension identifier.
    pub fn with_qualify_name(mut self, qualify_name: bool) -> Self {
        self.qualify_name = qualify_name;
        self
    }

    /// Set whether to include the extension version in the rendered output.
    pub fn with_extension_version(mut self, extension_version: bool) -> Self {
        self.extension_version = extension_version;
        self
    }

    /// Set whether to print type arguments in the rendered output.
    pub fn with_print_type_args(mut self, print_type_args: bool) -> Self {
        self.print_type_args = print_type_args;
        self
    }
}

impl Default for RenderStringConfig {
    fn default() -> Self {
        Self::new()
    }
}

/// Configuration for rendering a HUGR graph.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MermaidFormatter<'h, H: HugrInternals + ?Sized = Hugr> {
    /// The HUGR to render.
    hugr: &'h H,
    /// How to display the node indices.
    node_labels: NodeLabel<H::Node>,
    /// Show port offsets in the graph edges.
    port_offsets_in_edges: bool,
    /// Show type labels on edges.
    type_labels_in_edges: bool,
    /// A node to highlight as the graph entrypoint.
    entrypoint: Option<H::Node>,
    /// Include the version of the extension defining the operation.
    extension_version: bool,
    /// Include the operation's type arguments.
    print_type_args: bool,
    /// Qualify operation name with their extension identifier.
    qualify_name: bool,
}

impl<'h, H: HugrInternals + ?Sized> MermaidFormatter<'h, H> {
    /// Create a new [`MermaidFormatter`] for the given [`Hugr`].
    pub fn new(hugr: &'h H) -> Self {
        Self {
            hugr,
            node_labels: NodeLabel::Numeric,
            port_offsets_in_edges: true,
            type_labels_in_edges: true,
            entrypoint: None,
            extension_version: false,
            print_type_args: false,
            qualify_name: true,
        }
    }

    /// The entrypoint to highlight in the rendered graph.
    pub fn entrypoint(&self) -> Option<H::Node> {
        self.entrypoint
    }

    /// The rendering style of the node labels.
    pub fn node_labels(&self) -> &NodeLabel<H::Node> {
        &self.node_labels
    }

    /// Whether to show port offsets on edges.
    pub fn port_offsets(&self) -> bool {
        self.port_offsets_in_edges
    }

    /// Whether to show type labels on edges.
    pub fn type_labels(&self) -> bool {
        self.type_labels_in_edges
    }

    /// Whether to include the extension version in the rendered output.
    pub fn extension_version(&self) -> bool {
        self.extension_version
    }

    /// Whether to print type arguments in the rendered output.
    pub fn print_type_args(&self) -> bool {
        self.print_type_args
    }

    /// Whether to qualify operation name with their extension identifier.
    pub fn qualify_name(&self) -> bool {
        self.qualify_name
    }

    /// Set the node labels style.
    pub fn with_node_labels(mut self, node_labels: NodeLabel<H::Node>) -> Self {
        self.node_labels = node_labels;
        self
    }

    /// Set whether to show port offsets in edges.
    pub fn with_port_offsets(mut self, show: bool) -> Self {
        self.port_offsets_in_edges = show;
        self
    }

    /// Set whether to show type labels in edges.
    pub fn with_type_labels(mut self, show: bool) -> Self {
        self.type_labels_in_edges = show;
        self
    }

    /// Set whether to include the extension version in the rendered output.
    pub fn with_extension_version(mut self, show: bool) -> Self {
        self.extension_version = show;
        self
    }

    /// Set whether to print type arguments in the rendered output.
    pub fn with_print_type_args(mut self, show: bool) -> Self {
        self.print_type_args = show;
        self
    }

    /// Set whether to qualify operation name with their extension identifier.
    pub fn with_qualify_name(mut self, show: bool) -> Self {
        self.qualify_name = show;
        self
    }

    /// Set the entrypoint node to highlight.
    pub fn with_entrypoint(mut self, entrypoint: impl Into<Option<H::Node>>) -> Self {
        self.entrypoint = entrypoint.into();
        self
    }

    /// Render the graph into a Mermaid string.
    pub fn finish(self) -> String
    where
        H: HugrView,
    {
        self.hugr.mermaid_string_with_formatter(self)
    }

    pub(crate) fn with_hugr<NewH: HugrInternals<Node = H::Node>>(
        self,
        hugr: &NewH,
    ) -> MermaidFormatter<'_, NewH> {
        let MermaidFormatter {
            hugr: _,
            node_labels,
            port_offsets_in_edges,
            type_labels_in_edges,
            entrypoint,
            extension_version,
            print_type_args,
            qualify_name,
        } = self;
        MermaidFormatter {
            hugr,
            node_labels,
            port_offsets_in_edges,
            type_labels_in_edges,
            entrypoint,
            extension_version,
            print_type_args,
            qualify_name,
        }
    }
}

/// An error that occurs when trying to convert a `FullRenderConfig` into a
/// `RenderConfig`.
#[derive(Debug, thiserror::Error)]
pub enum UnsupportedRenderConfig {
    /// Custom node labels are not supported in the `RenderConfig` struct.
    #[error("Custom node labels are not supported in the `RenderConfig` struct")]
    CustomNodeLabels,
}

macro_rules! impl_mermaid_formatter_from {
    ($t:ty, $($lifetime:tt)?) => {
        impl<'h, $($lifetime,)? H: HugrView> From<MermaidFormatter<'h, $t>> for MermaidFormatter<'h, H> {
            fn from(value: MermaidFormatter<'h, $t>) -> Self {
                let MermaidFormatter {
                    hugr,
                    node_labels,
                    port_offsets_in_edges,
                    type_labels_in_edges,
                    entrypoint,
                    extension_version,
            print_type_args,
            qualify_name,
                } = value;
                MermaidFormatter {
                    hugr,
                    node_labels,
                    port_offsets_in_edges,
                    type_labels_in_edges,
                    entrypoint,
                    extension_version,
                    print_type_args,
                    qualify_name,
                }
            }
        }
    };
}

impl_mermaid_formatter_from!(&'hh H, 'hh);
impl_mermaid_formatter_from!(&'hh mut H, 'hh);
impl_mermaid_formatter_from!(std::rc::Rc<H>,);
impl_mermaid_formatter_from!(std::sync::Arc<H>,);
impl_mermaid_formatter_from!(Box<H>,);

impl<'h, H: HugrView + ToOwned> From<MermaidFormatter<'h, std::borrow::Cow<'_, H>>>
    for MermaidFormatter<'h, H>
{
    fn from(value: MermaidFormatter<'h, std::borrow::Cow<'_, H>>) -> Self {
        let MermaidFormatter {
            hugr,
            node_labels,
            port_offsets_in_edges,
            type_labels_in_edges,
            entrypoint,
            extension_version,
            print_type_args,
            qualify_name,
        } = value;
        MermaidFormatter {
            hugr,
            node_labels,
            port_offsets_in_edges,
            type_labels_in_edges,
            entrypoint,
            extension_version,
            print_type_args,
            qualify_name,
        }
    }
}

/// How to display the node indices.
#[derive(Default, Clone, Debug, PartialEq, Eq)]
pub enum NodeLabel<N: HugrNode = Node> {
    /// Do not display the node index.
    None,
    /// Display the node index as a number.
    #[default]
    Numeric,
    /// Display the numeric node index and a list of metadata keys and their JSON values.
    /// Prints "null" if a key is not present on a node.
    MetadataValues {
        /// List of metadata keys to display
        print_keys: Vec<String>,
    },
    /// Display the labels corresponding to the node indices.
    Custom(HashMap<N, String>),
}

/// Formatter method to compute a node style.
pub(in crate::hugr) fn node_style<'a>(
    h: &'a Hugr,
    formatter: MermaidFormatter<'a>,
) -> Box<dyn FnMut(NodeIndex) -> NodeStyle + 'a> {
    fn numeric_label(
        h: &Hugr,
        n: NodeIndex,
        is_entry: bool,
        inner_label_config: RenderStringConfig,
    ) -> String {
        if is_entry {
            format!(
                "({}) [**{}**]",
                n.index(),
                h.get_optype(n.into()).render_str(inner_label_config)
            )
        } else {
            format!(
                "({}) {}",
                n.index(),
                h.get_optype(n.into()).render_str(inner_label_config)
            )
        }
    }

    let mut entrypoint_style = PresentationStyle::default();
    entrypoint_style.stroke = Some("#832561".to_string());
    entrypoint_style.stroke_width = Some("3px".to_string());
    let entrypoint = formatter.entrypoint.map(Node::into_portgraph);
    let render_label_config = RenderStringConfig::new()
        .with_extension_version(formatter.extension_version())
        .with_print_type_args(formatter.print_type_args())
        .with_qualify_name(formatter.qualify_name());

    match formatter.node_labels {
        NodeLabel::Numeric => Box::new(move |n| {
            if Some(n) == entrypoint {
                NodeStyle::boxed(numeric_label(h, n, true, render_label_config))
                    .with_attrs(entrypoint_style.clone())
            } else {
                NodeStyle::boxed(numeric_label(h, n, false, render_label_config))
            }
        }),
        NodeLabel::None => Box::new(move |n| {
            if Some(n) == entrypoint {
                NodeStyle::boxed(format!(
                    "[**{name}**]",
                    name = h.get_optype(n.into()).render_str(render_label_config)
                ))
                .with_attrs(entrypoint_style.clone())
            } else {
                NodeStyle::boxed(h.get_optype(n.into()).render_str(render_label_config))
            }
        }),
        NodeLabel::MetadataValues { print_keys } => Box::new(move |n| {
            let kv_str = print_keys
                .iter()
                .filter_map(|key| {
                    h.get_metadata_any(n.into(), key).map(|json_value| {
                        format!(
                            "{key}={}",
                            serde_json::to_string(json_value)
                                .expect("JSON metadata should be serializable")
                                // the mermaid renderer in portgraph generates verbose escapes
                                // for double quotes and newlines, so we replace them with
                                // single quotes and spaces
                                .replace('\n', " ")
                                .replace('"', "\'")
                        )
                    })
                })
                .join("; ");

            if Some(n) == entrypoint {
                NodeStyle::boxed(format!(
                    "{}; {kv_str}",
                    numeric_label(h, n, true, render_label_config)
                ))
                .with_attrs(entrypoint_style.clone())
            } else {
                NodeStyle::boxed(format!(
                    "{}; {kv_str}",
                    numeric_label(h, n, false, render_label_config)
                ))
            }
        }),
        NodeLabel::Custom(labels) => Box::new(move |n| {
            if Some(n) == entrypoint {
                NodeStyle::boxed(format!(
                    "({label}) [**{name}**]",
                    label = labels.get(&n.into()).unwrap_or(&n.index().to_string()),
                    name = h.get_optype(n.into()).render_str(render_label_config)
                ))
                .with_attrs(entrypoint_style.clone())
            } else {
                NodeStyle::boxed(format!(
                    "({label}) {name}",
                    label = labels.get(&n.into()).unwrap_or(&n.index().to_string()),
                    name = h.get_optype(n.into()).render_str(render_label_config)
                ))
            }
        }),
    }
}

/// Formatter method to compute a port style.
pub(in crate::hugr) fn port_style(h: &Hugr) -> Box<dyn FnMut(PortIndex) -> PortStyle + '_> {
    let graph = &h.graph;
    Box::new(move |port| {
        let node = graph.port_node(port).unwrap();
        let optype = h.get_optype(node.into());
        let offset = graph.port_offset(port).unwrap();
        match optype.port_kind(offset).unwrap() {
            EdgeKind::Function(pf) => PortStyle::new(html_escape::encode_text(&format!("{pf}"))),
            EdgeKind::Const(ty) | EdgeKind::Value(ty) => {
                PortStyle::new(html_escape::encode_text(&format!("{ty}")))
            }
            EdgeKind::StateOrder => {
                if graph.port_links(port).count() > 0 {
                    PortStyle::text("", false)
                } else {
                    PortStyle::Hidden
                }
            }
            _ => PortStyle::text("", true),
        }
    })
}

/// Formatter method to compute an edge style.
#[allow(clippy::type_complexity)]
pub(in crate::hugr) fn edge_style<'a>(
    h: &'a Hugr,
    config: MermaidFormatter<'_>,
) -> Box<
    dyn FnMut(
            <MultiPortGraph<u32, u32, u32> as LinkView>::LinkEndpoint,
            <MultiPortGraph<u32, u32, u32> as LinkView>::LinkEndpoint,
        ) -> EdgeStyle
        + 'a,
> {
    let graph = &h.graph;
    let render_label_config = RenderStringConfig::new()
        .with_extension_version(config.extension_version())
        .with_print_type_args(config.print_type_args())
        .with_qualify_name(config.qualify_name());
    Box::new(move |src, tgt| {
        let src_node = graph.port_node(src).unwrap();
        let src_optype = h.get_optype(src_node.into());
        let src_offset = graph.port_offset(src).unwrap();
        let tgt_offset = graph.port_offset(tgt).unwrap();

        let port_kind = src_optype.port_kind(src_offset).unwrap();

        // StateOrder edges: Dotted line.
        // Control flow edges: Dashed line.
        // Static and Value edges: Solid line with label.
        let style = match port_kind {
            EdgeKind::StateOrder => EdgeStyle::Dotted,
            EdgeKind::ControlFlow => EdgeStyle::Dashed,
            EdgeKind::Const(_) | EdgeKind::Function(_) | EdgeKind::Value(_) => EdgeStyle::Solid,
        };

        // Compute the label for the edge, given the setting flags.
        fn type_label(e: EdgeKind, config: RenderStringConfig) -> Option<String> {
            match e {
                EdgeKind::Const(ty) | EdgeKind::Value(ty) => Some(ty.render_str(config)),
                EdgeKind::Function(pf) => Some(pf.render_str(config)),
                _ => None,
            }
        }
        //
        // Only static and value edges have types to display.
        let label = match (
            config.port_offsets_in_edges,
            type_label(port_kind, render_label_config).filter(|_| config.type_labels_in_edges),
        ) {
            (true, Some(ty)) => {
                format!("{}:{}\n{ty}", src_offset.index(), tgt_offset.index())
            }
            (true, _) => format!("{}:{}", src_offset.index(), tgt_offset.index()),
            (false, Some(ty)) => ty.to_string(),
            _ => return style,
        };
        style.with_label(label)
    })
}

#[cfg(test)]
mod tests {
    use crate::{
        NodeIndex,
        builder::{DFGBuilder, Dataflow, DataflowHugr, test::simple_dfg_hugr},
        extension::prelude::bool_t,
        std_extensions::arithmetic::{int_ops::IntOpDef, int_types::int_type},
        types::Signature,
    };

    use super::*;

    #[cfg_attr(miri, ignore)] // Opening files is not supported in (isolated) miri
    #[test]
    fn test_custom_node_labels() {
        let h = simple_dfg_hugr();
        let node_labels = h
            .nodes()
            .map(|n| (n, format!("node_{}", n.index())))
            .collect();
        let config = h
            .mermaid_format()
            .with_node_labels(NodeLabel::Custom(node_labels));
        insta::assert_snapshot!(h.mermaid_string_with_formatter(config));
    }

    #[test]
    fn render_string_config_is_applied_to_node_labels() {
        let int_type = int_type(5);
        let mut builder =
            DFGBuilder::new(Signature::new([int_type.clone(), int_type], [bool_t()])).unwrap();
        let [lhs, rhs] = builder.input_wires_arr();
        let output = builder
            .add_dataflow_op(IntOpDef::ieq.with_log_width(5), [lhs, rhs])
            .unwrap()
            .out_wire(0);
        let h = builder.finish_hugr_with_outputs([output]).unwrap();

        let options_on = h
            .mermaid_format()
            .with_extension_version(true)
            .with_print_type_args(true)
            .with_qualify_name(true)
            .finish();
        let unqualified = h
            .mermaid_format()
            .with_extension_version(false)
            .with_print_type_args(false)
            .with_qualify_name(false)
            .finish();

        assert!(options_on.contains("arithmetic.int.ieq<5>@0.1.1"));
        assert!(!unqualified.contains("arithmetic.int.ieq"));
        assert!(unqualified.contains("ieq"));

        assert!(options_on.contains("<br>arithmetic.int.types.int<5>@0.1.0"));
        assert!(!unqualified.contains("<br>arithmetic.int.types.int"));
        assert!(unqualified.contains("<br>int"));
    }
}
