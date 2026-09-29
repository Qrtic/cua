//! macOS Accessibility (AX) API bindings and tree walker.
//!
//! # AX element indexing
//! Every *actionable* element in the tree is assigned an `element_index` (0-based,
//! depth-first). The index is stable within a single `get_window_state` snapshot
//! and is passed to `click`, `type_text`, etc. to identify the target element
//! without requiring pixel coordinates.
//!
//! # Tree format (treeMarkdown)
//! ```text
//!   - [0] AXButton "OK" [actions=[press]]
//!     - AXStaticText = "OK"
//!   - [1] AXTextField "Name" [value="John"]
//! ```
//! - Indexed elements: `- [N] AXRole "Title" [key=val ...]`
//! - Non-indexed (no actions, not interesting): `- AXRole = "value"`
//! - 2-space indent per depth level

pub(crate) mod app_context;
pub(crate) mod application_menu;
pub(crate) mod attached_popover;
pub(crate) mod attached_sheet;
pub mod bindings;
pub mod cache;
pub(crate) mod date_value;
mod element_ancestry;
pub(crate) mod embedded_menu;
pub mod enablement;
pub mod exact_target;
pub(crate) mod focused_panel;
pub(crate) mod menu_context;
pub(crate) mod menu_selection;
mod menu_window_diagnostics;
pub(crate) mod native_text_editor;
pub mod tree;
mod virtual_button;
pub(crate) mod window_classification;
pub mod window_scope;
pub(crate) mod window_tabs;

pub use cache::ElementCache;
pub use tree::{
    walk_tree, walk_tree_bounded, AXNode, TreeWalkResult, DEFAULT_MAX_DEPTH, DEFAULT_MAX_ELEMENTS,
};
pub use window_scope::WindowScope;
