//! Helper methods to compute the node/edge/port style when rendering a HUGR
//! into dot or mermaid format.

use itertools::Itertools;
use std::collections::HashMap;

use portgraph::render::{EdgeStyle, NodeStyle, PortStyle, PresentationStyle};
use portgraph::{LinkView, MultiPortGraph, NodeIndex, PortIndex, PortView};

use crate::core::HugrNode;
use crate::hugr::internal::HugrInternals;
use crate::ops::{OpTrait, RenderStringConfig};
use crate::types::EdgeKind;
use crate::{Hugr, HugrView, Node};

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
    /// How operation names are rendered in node labels.
    render_string_config: RenderStringConfig,
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
            render_string_config: RenderStringConfig {
                qualify_name: true,
                ..Default::default()
            },
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

    /// The configuration used to render operation names in node labels.
    pub fn render_string_config(&self) -> RenderStringConfig {
        self.render_string_config
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

    /// Set how operation names are rendered in node labels.
    pub fn with_render_string_config(mut self, config: RenderStringConfig) -> Self {
        self.render_string_config = config;
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
            render_string_config,
        } = self;
        MermaidFormatter {
            hugr,
            node_labels,
            port_offsets_in_edges,
            type_labels_in_edges,
            entrypoint,
            render_string_config,
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
                    render_string_config,
                } = value;
                MermaidFormatter {
                    hugr,
                    node_labels,
                    port_offsets_in_edges,
                    type_labels_in_edges,
                    entrypoint,
                    render_string_config,
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
            render_string_config,
        } = value;
        MermaidFormatter {
            hugr,
            node_labels,
            port_offsets_in_edges,
            type_labels_in_edges,
            entrypoint,
            render_string_config,
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
    fn node_name(h: &Hugr, n: NodeIndex, inner_label_config: RenderStringConfig) -> String {
        // Nicola: todo: Move the logic in OpTrait -> use a struct for setting parameters -> flag for ext version, types args, qualifying names
        // the stuff inside optype implement optrait
        h.get_optype(n.into()).render_str(inner_label_config)
    }

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
                node_name(h, n, inner_label_config)
            )
        } else {
            format!("({}) {}", n.index(), node_name(h, n, inner_label_config))
        }
    }

    let mut entrypoint_style = PresentationStyle::default();
    entrypoint_style.stroke = Some("#832561".to_string());
    entrypoint_style.stroke_width = Some("3px".to_string());
    let entrypoint = formatter.entrypoint.map(Node::into_portgraph);
    let render_label_config = formatter.render_string_config();

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
                    name = node_name(h, n, render_label_config)
                ))
                .with_attrs(entrypoint_style.clone())
            } else {
                NodeStyle::boxed(node_name(h, n, render_label_config))
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
                    name = node_name(h, n, render_label_config)
                ))
                .with_attrs(entrypoint_style.clone())
            } else {
                NodeStyle::boxed(format!(
                    "({label}) {name}",
                    label = labels.get(&n.into()).unwrap_or(&n.index().to_string()),
                    name = node_name(h, n, render_label_config)
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
                EdgeKind::Const(ty) | EdgeKind::Value(ty) => {
                    Some(format!("{}", ty.render_str(config)))
                }
                // todo: use the render_str method for function types
                EdgeKind::Function(pf) => Some(format!("Function§{pf}")),
                _ => None,
            }
        }
        //
        // Only static and value edges have types to display.
        let label = match (
            config.port_offsets_in_edges,
            type_label(port_kind, config.render_string_config)
                .filter(|_| config.type_labels_in_edges),
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
        builder::{Container, DFGBuilder, Dataflow, DataflowHugr, test::simple_dfg_hugr},
        extension::{ExtensionId, Version, prelude::bool_t},
        ops::custom::OpaqueOp,
        std_extensions::{
            arithmetic::{int_ops::IntOpDef, int_types::int_type},
            collections::array::{Array, ArrayKind},
        },
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
        insta::assert_snapshot!(h.mermaid_string_with_formatter(config.clone()));
        std::fs::write(
            "test_custom_node_labels.mmd",
            h.mermaid_string_with_formatter(config),
        )
        .unwrap();
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

        let qualified = h.mermaid_format().finish();
        let unqualified = h
            .mermaid_format()
            .with_render_string_config(RenderStringConfig::default())
            .finish();

        assert!(qualified.contains("arithmetic.int.ieq"));
        assert!(!unqualified.contains("arithmetic.int.ieq"));
        assert!(unqualified.contains("ieq"));
    }

    #[cfg_attr(miri, ignore)] // Opening files is not supported in (isolated) miri
    #[test]
    fn write_extension_version_examples() {
        let int_type = int_type(5);

        let mut custom_op_hugr = DFGBuilder::new(Signature::new(
            [int_type.clone(), int_type.clone()],
            [bool_t()],
        ))
        .unwrap();
        let [lhs, rhs] = custom_op_hugr.input_wires_arr();
        let result = custom_op_hugr
            .add_dataflow_op(IntOpDef::ieq.with_log_width(5), [lhs, rhs])
            .unwrap()
            .out_wire(0);
        let test_op = OpaqueOp::new(
            ExtensionId::new_unchecked("TEST_EXT.name"),
            Version::parse("1.0.0-parsdefrve").unwrap(),
            "TestOp",
            [],
            Signature::new_endo([bool_t()]),
        );
        let result = custom_op_hugr
            .add_dataflow_op(test_op, [result])
            .unwrap()
            .out_wire(0);
        custom_op_hugr.set_outputs([result]).unwrap();
        let custom_op_hugr = custom_op_hugr.hugr().clone();

        let array_type = Array::ty(3, int_type.clone());
        let array_hugr = DFGBuilder::new(Signature::new_endo([array_type])).unwrap();
        let [array] = array_hugr.input_wires_arr();
        let array_hugr = array_hugr.finish_hugr_with_outputs([array]).unwrap();

        let mut int_op_hugr =
            DFGBuilder::new(Signature::new([int_type.clone(), int_type], [bool_t()])).unwrap();
        let [lhs, rhs] = int_op_hugr.input_wires_arr();
        let result = int_op_hugr
            .add_dataflow_op(IntOpDef::ieq.with_log_width(5), [lhs, rhs])
            .unwrap()
            .out_wire(0);
        let int_op_hugr = int_op_hugr.finish_hugr_with_outputs([result]).unwrap();

        for (name, hugr) in [
            ("test_custom_op_version.mmd", custom_op_hugr),
            ("test_nested_type_version.mmd", array_hugr),
            ("test_type_arg_version.mmd", int_op_hugr),
        ] {
            std::fs::write(
                name,
                hugr.mermaid_string_with_config(RenderStringConfig {
                    qualify_name: false,
                    extension_version: true,
                    print_type_args: true,
                }),
            )
            .unwrap();
        }
    }
}
