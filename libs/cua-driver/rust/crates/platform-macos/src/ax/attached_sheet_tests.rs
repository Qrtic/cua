use super::*;
use std::{cell::Cell, collections::HashMap};

#[derive(Clone)]
struct Entry {
    role: &'static str,
    id: &'static str,
    owner: i32,
    parent: Option<u32>,
    window: Option<u32>,
    children: Vec<u32>,
    minimized: Result<bool, AXError>,
    visible: bool,
}

struct Tree {
    nodes: HashMap<u32, Entry>,
    focused: u32,
    windows: Vec<u32>,
    reads: Cell<u32>,
    change_focus: bool,
    budget: Cell<usize>,
}

impl SheetTree for Tree {
    type Node = u32;
    fn focused(&self) -> Option<u32> {
        let n = self.reads.get();
        self.reads.set(n + 1);
        (!(self.change_focus && n > 0)).then_some(self.focused)
    }
    fn windows(&self) -> Option<Vec<u32>> {
        Some(self.windows.clone())
    }
    fn role(&self, n: &u32) -> Option<String> {
        Some(self.nodes.get(n)?.role.into())
    }
    fn identifier(&self, n: &u32) -> Option<String> {
        Some(self.nodes.get(n)?.id.into())
    }
    fn owner(&self, n: &u32) -> Option<i32> {
        Some(self.nodes.get(n)?.owner)
    }
    fn window_id(&self, n: &u32) -> Option<u32> {
        self.nodes.contains_key(n).then_some(*n)
    }
    fn relation(&self, n: &u32, name: &str) -> Option<u32> {
        match name {
            "AXParent" => self.nodes.get(n)?.parent,
            "AXWindow" => self.nodes.get(n)?.window,
            _ => None,
        }
    }
    fn contains_child(&self, parent: &u32, child: &u32) -> bool {
        self.nodes
            .get(parent)
            .is_some_and(|n| n.children.contains(child))
    }
    fn same(&self, a: &u32, b: &u32) -> bool {
        a == b
    }
    fn owns_window(&self, pid: i32, id: u32) -> bool {
        self.nodes.get(&id).is_some_and(|n| n.owner == pid)
    }
    fn minimized(&self, n: &u32) -> Result<bool, AXError> {
        self.nodes[n].minimized
    }
    fn on_screen(&self, pid: i32, id: u32) -> bool {
        self.nodes
            .get(&id)
            .is_some_and(|n| n.owner == pid && n.visible)
    }
    fn within_budget(&self) -> bool {
        let n = self.budget.get();
        self.budget.set(n.saturating_sub(1));
        n > 0
    }
}

fn xcode() -> Tree {
    let entry = |role, id, parent, children| Entry {
        role,
        id,
        owner: 42,
        parent,
        window: Some(700),
        children,
        minimized: Err(kAXErrorAttributeUnsupported),
        visible: true,
    };
    let mut nodes = HashMap::from([
        (
            700,
            entry("AXWindow", "Xcode.WorkspaceWindow", None, vec![900]),
        ),
        (900, entry("AXSheet", "save-panel", Some(700), vec![950])),
        (950, entry("AXSheet", "GoToWindow", Some(900), vec![])),
    ]);
    nodes.get_mut(&700).unwrap().minimized = Ok(false);
    Tree {
        nodes,
        focused: 950,
        windows: vec![700],
        reads: Cell::new(0),
        change_focus: false,
        budget: Cell::new(1000),
    }
}

#[test]
fn xcode_go_to_folder_keeps_its_physical_window_and_ultimate_document_host() {
    let tree = xcode();
    assert_eq!(prove(&tree, 42, 950), Some(950));
    assert_eq!(dialog_host(&tree, 42, 950), Some(700));
    let chain = dialog_chain(&tree, 42, 950).unwrap();
    assert_eq!(chain.window_ids, [950, 900, 700]);
    assert_eq!(prove_with_visibility(&tree, 42, 950, true), Some(950));
    // Neither the parent panel nor a guessed sibling substitutes for the leaf.
    assert!(prove(&tree, 42, 900).is_none());
    assert!(prove(&tree, 42, 951).is_none());
}

#[test]
fn nested_panel_requires_every_reciprocal_link_and_the_real_axwindow_host() {
    for id in [950, 900] {
        let mut tree = xcode();
        let parent = tree.nodes[&id].parent.unwrap();
        tree.nodes.get_mut(&parent).unwrap().children.clear();
        assert!(prove(&tree, 42, 950).is_none());
        let mut tree = xcode();
        tree.nodes.get_mut(&id).unwrap().window = Some(951);
        assert!(prove(&tree, 42, 950).is_none());
    }
    let mut tree = xcode();
    tree.nodes.get_mut(&900).unwrap().parent = Some(950);
    tree.nodes.get_mut(&950).unwrap().children.push(900);
    assert!(prove(&tree, 42, 950).is_none());
}

#[test]
fn nested_dialog_refuses_foreign_hidden_minimized_or_nonstandard_ancestors() {
    for id in [950, 900, 700] {
        let mut tree = xcode();
        tree.nodes.get_mut(&id).unwrap().owner = 99;
        assert!(dialog_host(&tree, 42, 950).is_none());
        for state in [Ok(true), Err(crate::ax::bindings::kAXErrorCannotComplete)] {
            let mut tree = xcode();
            tree.nodes.get_mut(&id).unwrap().minimized = state;
            assert!(dialog_host(&tree, 42, 950).is_none());
        }
        let mut tree = xcode();
        tree.nodes.get_mut(&id).unwrap().visible = false;
        assert!(dialog_host(&tree, 42, 950).is_none());
    }
    let mut tree = xcode();
    tree.nodes.get_mut(&900).unwrap().id = "unrelated-confirmation";
    assert!(prove(&tree, 42, 950).is_some());
    assert!(dialog_host(&tree, 42, 950).is_none());
}

#[test]
fn changed_focus_unlisted_host_and_exhausted_reads_never_grant_nested_target() {
    let mut tree = xcode();
    tree.change_focus = true;
    assert!(prove(&tree, 42, 950).is_none());
    for windows in [vec![], vec![700, 700], vec![900]] {
        let mut tree = xcode();
        tree.windows = windows;
        assert!(prove(&tree, 42, 950).is_none());
    }
    for budget in [0, 2, 5] {
        let tree = xcode();
        tree.budget.set(budget);
        assert!(prove(&tree, 42, 950).is_none());
    }
}
