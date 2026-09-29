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
    children_complete: bool,
    host_child_reads: Cell<usize>,
    new_sibling_after_selection: bool,
    unreadable_identifier: Option<u32>,
    leaf_child_reads: Cell<usize>,
    new_child_after_leaf_check: bool,
    windows_reads: Cell<usize>,
    relation_reads: Cell<usize>,
    relation_fault: Option<RelationFault>,
    identifier_reads: Cell<usize>,
    identifier_after_first: Option<&'static str>,
    identifier_unreadable_after_first: bool,
    expire_on_parent_read: bool,
}

#[derive(Clone, Copy)]
enum RelationFault {
    Reparented,
    WrongWindow,
    Unreadable,
}

impl SheetTree for Tree {
    type Node = u32;
    fn focused(&self) -> Option<u32> {
        let n = self.reads.get();
        self.reads.set(n + 1);
        (!(self.change_focus && n > 0)).then_some(self.focused)
    }
    fn windows(&self) -> Option<Vec<u32>> {
        self.windows_reads.set(self.windows_reads.get() + 1);
        Some(self.windows.clone())
    }
    fn role(&self, n: &u32) -> Option<String> {
        Some(self.nodes.get(n)?.role.into())
    }
    fn identifier(&self, n: &u32) -> Option<String> {
        if self.unreadable_identifier == Some(*n) {
            return None;
        }
        if *n == 900 {
            let reads = self.identifier_reads.get();
            self.identifier_reads.set(reads + 1);
            if reads > 0 {
                if self.identifier_unreadable_after_first {
                    return None;
                }
                if let Some(identifier) = self.identifier_after_first {
                    return Some(identifier.into());
                }
            }
        }
        Some(self.nodes.get(n)?.id.into())
    }
    fn owner(&self, n: &u32) -> Option<i32> {
        Some(self.nodes.get(n)?.owner)
    }
    fn window_id(&self, n: &u32) -> Option<u32> {
        self.nodes.contains_key(n).then_some(*n)
    }
    fn relation(&self, n: &u32, name: &str) -> Option<u32> {
        let reads = self.relation_reads.get();
        self.relation_reads.set(reads + 1);
        if self.expire_on_parent_read && name == "AXParent" {
            self.budget.set(0);
        }
        if *n == 900 && reads > 0 {
            match (self.relation_fault, name) {
                (Some(RelationFault::Reparented), "AXParent") => return Some(701),
                (Some(RelationFault::WrongWindow), "AXWindow") => return Some(701),
                (Some(RelationFault::Unreadable), "AXParent") => return None,
                _ => {}
            }
        }
        match name {
            "AXParent" => self.nodes.get(n)?.parent,
            "AXWindow" => self.nodes.get(n)?.window,
            _ => None,
        }
    }
    fn child_sheets(&self, n: &u32) -> Option<Vec<u32>> {
        if !self.children_complete {
            return None;
        }
        if *n == 900 {
            let reads = self.leaf_child_reads.get();
            self.leaf_child_reads.set(reads + 1);
            if self.new_child_after_leaf_check && reads > 0 {
                return Some(vec![950]);
            }
        }
        if *n == 700 {
            let reads = self.host_child_reads.get();
            self.host_child_reads.set(reads + 1);
            if self.new_sibling_after_selection && reads > 0 {
                return Some(vec![900, 901]);
            }
        }
        let mut sheets = Vec::new();
        for child in &self.nodes.get(n)?.children {
            if self.nodes.get(child)?.role == "AXSheet" {
                sheets.push(*child);
            }
        }
        Some(sheets)
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
        children_complete: true,
        host_child_reads: Cell::new(0),
        new_sibling_after_selection: false,
        unreadable_identifier: None,
        leaf_child_reads: Cell::new(0),
        new_child_after_leaf_check: false,
        windows_reads: Cell::new(0),
        relation_reads: Cell::new(0),
        relation_fault: None,
        identifier_reads: Cell::new(0),
        identifier_after_first: None,
        identifier_unreadable_after_first: false,
        expire_on_parent_read: false,
    }
}

fn chess_with_host_focus() -> Tree {
    let mut tree = xcode();
    tree.nodes.remove(&950);
    tree.nodes.get_mut(&900).unwrap().children.clear();
    tree.nodes.get_mut(&900).unwrap().id = "_NS:394";
    tree.nodes.get_mut(&700).unwrap().id = "_NS:582";
    tree.focused = 700;
    tree
}

#[test]
fn standard_dialog_attachment_retains_exact_panel_and_host() {
    for identifier in ["save-panel", "open-panel"] {
        let mut tree = xcode();
        tree.nodes.get_mut(&900).unwrap().id = identifier;
        assert_eq!(
            dialog_attachment(&tree, 42, 950),
            Some(DialogAttachment {
                window_id: 950,
                panel_id: 900,
                host_id: 700,
                path: vec![950, 900, 700],
            })
        );
        assert_eq!(
            tree.identifier_reads.get(),
            2,
            "the final standard-panel identifier must be read after the double chain proof"
        );
    }
}

#[test]
fn standard_dialog_attachment_refuses_identifier_changed_after_chain_proof() {
    let mut weaker = xcode();
    weaker.identifier_after_first = Some("ordinary-confirmation");
    assert_eq!(
        dialog_host(&weaker, 42, 950),
        Some(700),
        "a structural host proof alone does not include the required final identifier read"
    );
    let mut tree = xcode();
    tree.identifier_after_first = Some("ordinary-confirmation");
    assert!(dialog_attachment(&tree, 42, 950).is_none());
    assert_eq!(tree.identifier_reads.get(), 2);
}

#[test]
fn standard_dialog_attachment_refuses_identifier_failure_after_chain_proof() {
    let mut weaker = xcode();
    weaker.identifier_unreadable_after_first = true;
    assert_eq!(dialog_host(&weaker, 42, 950), Some(700));
    let mut tree = xcode();
    tree.identifier_unreadable_after_first = true;
    assert!(dialog_attachment(&tree, 42, 950).is_none());
    assert_eq!(tree.identifier_reads.get(), 2);
}

#[test]
fn standard_dialog_probe_declines_direct_ordinary_before_full_proof() {
    let mut tree = chess_with_host_focus();
    tree.focused = 900;
    let probe = probe_standard_dialog(&tree, 42, 900);
    assert!(probe.observed_requested_sheet);
    assert_eq!(probe.host_id, None);
    assert_eq!(tree.identifier_reads.get(), 1);
    assert_eq!(tree.windows_reads.get(), 0);
    assert_eq!(
        tree.relation_reads.get(),
        1,
        "only the existing direct-parent discovery"
    );

    let mut original = chess_with_host_focus();
    original.focused = 900;
    assert!(dialog_attachment(&original, 42, 900).is_none());
    assert_eq!(original.identifier_reads.get(), 1);
    assert_eq!(original.windows_reads.get(), 1);
    assert_eq!(original.relation_reads.get(), 3);
    // Declining optional preparation cannot stand in for keyboard authority.
    assert!(keyboard_activation_chain(&tree, 42, 900).is_some());
    tree.nodes.get_mut(&700).unwrap().children.clear();
    assert!(keyboard_activation_chain(&tree, 42, 900).is_none());
}

#[test]
fn standard_dialog_probe_direct_standard_retains_double_proof_and_final_identifier() {
    for identifier in ["save-panel", "open-panel"] {
        let mut tree = chess_with_host_focus();
        tree.focused = 900;
        tree.nodes.get_mut(&900).unwrap().id = identifier;
        let probe = probe_standard_dialog(&tree, 42, 900);
        assert!(probe.observed_requested_sheet);
        assert_eq!(probe.host_id, Some(700));
        assert_eq!(tree.windows_reads.get(), 2);
        assert_eq!(tree.identifier_reads.get(), 2);

        let mut original = chess_with_host_focus();
        original.focused = 900;
        original.nodes.get_mut(&900).unwrap().id = identifier;
        assert_eq!(dialog_attachment(&original, 42, 900).unwrap().host_id, 700);
        assert_eq!(tree.windows_reads.get(), original.windows_reads.get());
        assert_eq!(tree.relation_reads.get(), original.relation_reads.get());
        assert_eq!(tree.identifier_reads.get(), original.identifier_reads.get());
        assert_eq!(tree.reads.get(), original.reads.get());
    }
}

#[test]
fn standard_dialog_probe_keeps_nested_standard_ancestor_and_original_read_counts() {
    let tree = xcode();
    let probe = probe_standard_dialog(&tree, 42, 950);
    assert!(probe.observed_requested_sheet);
    assert_eq!(
        probe.host_id,
        Some(700),
        "GoToWindow is not the standard ancestor"
    );
    let original = xcode();
    assert_eq!(dialog_attachment(&original, 42, 950).unwrap().panel_id, 900);
    assert_eq!(tree.windows_reads.get(), original.windows_reads.get());
    assert_eq!(tree.relation_reads.get(), original.relation_reads.get());
    assert_eq!(tree.identifier_reads.get(), original.identifier_reads.get());
    assert_eq!(tree.reads.get(), original.reads.get());
}

#[test]
fn standard_dialog_probe_unknown_direct_identifier_keeps_original_full_proof() {
    for unreadable in [false, true] {
        let mut tree = chess_with_host_focus();
        tree.focused = 900;
        tree.nodes.get_mut(&900).unwrap().id = "";
        tree.unreadable_identifier = unreadable.then_some(900);
        let probe = probe_standard_dialog(&tree, 42, 900);
        assert!(probe.observed_requested_sheet);
        assert_eq!(probe.host_id, None);
        assert_eq!(
            tree.windows_reads.get(),
            1,
            "unknown cannot take the early decline"
        );
        assert_eq!(tree.relation_reads.get(), 3);
        if !unreadable {
            assert_eq!(
                tree.identifier_reads.get(),
                2,
                "unknown is reread at the original point"
            );
        }
    }
    let mut later_standard = chess_with_host_focus();
    later_standard.focused = 900;
    later_standard.nodes.get_mut(&900).unwrap().id = "";
    later_standard.identifier_after_first = Some("save-panel");
    assert_eq!(
        probe_standard_dialog(&later_standard, 42, 900).host_id,
        Some(700)
    );
    assert_eq!(later_standard.windows_reads.get(), 2);
    assert_eq!(
        later_standard.identifier_reads.get(),
        3,
        "an early unknown must not replace the original later standard-panel decision"
    );
}

#[test]
fn standard_dialog_probe_rechecks_identifier_after_retained_standard_proof() {
    for unreadable in [false, true] {
        let mut tree = chess_with_host_focus();
        tree.focused = 900;
        tree.nodes.get_mut(&900).unwrap().id = "save-panel";
        tree.identifier_unreadable_after_first = unreadable;
        tree.identifier_after_first = (!unreadable).then_some("ordinary-confirmation");
        let probe = probe_standard_dialog(&tree, 42, 900);
        assert!(probe.observed_requested_sheet);
        assert_eq!(probe.host_id, None);
        assert_eq!(tree.windows_reads.get(), 2);
        assert_eq!(
            tree.identifier_reads.get(),
            2,
            "early standard ID is never final authority"
        );
    }
}

#[test]
fn standard_dialog_probe_retained_relation_selection_and_budget_failures_stay_negative() {
    for fault in [
        RelationFault::Reparented,
        RelationFault::WrongWindow,
        RelationFault::Unreadable,
    ] {
        let mut tree = chess_with_host_focus();
        tree.focused = 900;
        tree.nodes.get_mut(&900).unwrap().id = "save-panel";
        tree.relation_fault = Some(fault);
        let probe = probe_standard_dialog(&tree, 42, 900);
        assert!(probe.observed_requested_sheet);
        assert_eq!(probe.host_id, None);
    }
    for expire in [false, true] {
        let mut tree = chess_with_host_focus();
        tree.focused = 900;
        tree.nodes.get_mut(&900).unwrap().id = "save-panel";
        tree.change_focus = !expire;
        tree.expire_on_parent_read = expire;
        let probe = probe_standard_dialog(&tree, 42, 900);
        assert!(probe.observed_requested_sheet);
        assert_eq!(probe.host_id, None);
    }
}

#[test]
fn standard_dialog_probe_hint_requires_observed_exact_same_pid_sheet() {
    for (pid, requested) in [(43, 900), (42, 901), (42, 700)] {
        let mut tree = chess_with_host_focus();
        tree.focused = 900;
        let probe = probe_standard_dialog(&tree, pid, requested);
        assert!(!probe.observed_requested_sheet);
        assert_eq!(probe.host_id, None);
    }
}

#[test]
fn ordinary_sheet_keyboard_activation_requires_its_own_proven_visible_leaf() {
    for focus in [700, 900] {
        let mut tree = chess_with_host_focus();
        tree.focused = focus;
        let proof = keyboard_activation_chain(&tree, 42, 900).unwrap();
        assert_eq!(proof.window_ids, [900, 700]);
        assert!(keyboard_activation_matches(&tree, 42, 900, &proof));
        assert!(keyboard_activation_chain(&tree, 42, 700).is_none());
        assert!(keyboard_activation_chain(&tree, 42, 901).is_none());
        assert!(
            dialog_host(&tree, 42, 900).is_none(),
            "keyboard activation must not grant file-dialog segment authority"
        );
    }
    let mut tree = xcode();
    tree.nodes.get_mut(&900).unwrap().id = "ordinary-settings";
    tree.nodes.get_mut(&950).unwrap().id = "ordinary-confirmation";
    assert_eq!(
        keyboard_activation_chain(&tree, 42, 950)
            .unwrap()
            .window_ids,
        [950, 900, 700]
    );
    assert!(keyboard_activation_chain(&tree, 42, 900).is_none());
    assert!(dialog_host(&tree, 42, 950).is_none());
}

#[test]
fn ordinary_sheet_keyboard_activation_does_not_reclassify_file_panels() {
    for identifier in ["save-panel", "open-panel"] {
        let mut tree = xcode();
        tree.nodes.get_mut(&900).unwrap().id = identifier;
        assert!(keyboard_activation_chain(&tree, 42, 950).is_none());
        assert_eq!(dialog_host(&tree, 42, 950), Some(700));
        tree.unreadable_identifier = Some(900);
        assert!(dialog_host(&tree, 42, 950).is_none());
        assert!(
            keyboard_activation_chain(&tree, 42, 950).is_none(),
            "an unreadable file panel cannot cross into ordinary-sheet admission"
        );
    }
    let mut tree = chess_with_host_focus();
    tree.unreadable_identifier = Some(900);
    assert!(keyboard_activation_chain(&tree, 42, 900).is_none());
    // A readable empty identifier is different from an AX read failure.
    tree.unreadable_identifier = None;
    tree.nodes.get_mut(&900).unwrap().id = "";
    assert!(keyboard_activation_chain(&tree, 42, 900).is_some());
}

#[test]
fn focused_sheet_keyboard_activation_refuses_new_children_before_focus_updates() {
    let mut tree = xcode();
    tree.nodes.get_mut(&900).unwrap().id = "ordinary-settings";
    tree.focused = 900;
    assert!(
        prove(&tree, 42, 900).is_some(),
        "legacy discovery is unchanged"
    );
    assert!(keyboard_activation_chain(&tree, 42, 900).is_none());

    let mut tree = chess_with_host_focus();
    tree.focused = 900;
    tree.new_child_after_leaf_check = true;
    assert!(
        keyboard_activation_chain(&tree, 42, 900).is_none(),
        "a child appearing during proof cannot inherit the stale focused-sheet authority"
    );
}

#[test]
fn ordinary_sheet_keyboard_activation_refuses_foreign_stale_or_unreadable_chains() {
    for alter in [
        |t: &mut Tree| t.nodes.get_mut(&900).unwrap().owner = 99,
        |t: &mut Tree| t.nodes.get_mut(&700).unwrap().owner = 99,
        |t: &mut Tree| t.nodes.get_mut(&900).unwrap().role = "AXGroup",
        |t: &mut Tree| t.nodes.get_mut(&700).unwrap().role = "AXGroup",
        |t: &mut Tree| t.nodes.get_mut(&900).unwrap().parent = Some(900),
        |t: &mut Tree| t.nodes.get_mut(&900).unwrap().window = Some(701),
        |t: &mut Tree| t.nodes.get_mut(&700).unwrap().children.clear(),
        |t: &mut Tree| t.nodes.get_mut(&900).unwrap().visible = false,
        |t: &mut Tree| t.nodes.get_mut(&700).unwrap().visible = false,
        |t: &mut Tree| t.nodes.get_mut(&700).unwrap().minimized = Ok(true),
        |t: &mut Tree| {
            t.nodes.get_mut(&900).unwrap().minimized =
                Err(crate::ax::bindings::kAXErrorCannotComplete)
        },
        |t: &mut Tree| t.windows = vec![700, 700],
        |t: &mut Tree| t.windows = vec![],
        |t: &mut Tree| t.children_complete = false,
        |t: &mut Tree| t.change_focus = true,
        |t: &mut Tree| t.new_sibling_after_selection = true,
        |t: &mut Tree| t.budget.set(0),
    ] {
        let mut tree = chess_with_host_focus();
        alter(&mut tree);
        assert!(keyboard_activation_chain(&tree, 42, 900).is_none());
    }
}

#[test]
fn ordinary_sheet_keyboard_activation_revalidates_before_each_use_without_renewing_budget() {
    for alter in [
        |t: &mut Tree| t.nodes.get_mut(&700).unwrap().children.clear(),
        |t: &mut Tree| t.nodes.get_mut(&900).unwrap().visible = false,
        |t: &mut Tree| t.nodes.get_mut(&900).unwrap().owner = 99,
        |t: &mut Tree| t.unreadable_identifier = Some(900),
        |t: &mut Tree| t.nodes.get_mut(&900).unwrap().id = "save-panel",
        |t: &mut Tree| t.budget.set(0),
        |t: &mut Tree| t.nodes.get_mut(&900).unwrap().parent = None,
        |t: &mut Tree| t.nodes.get_mut(&900).unwrap().parent = Some(901),
        |t: &mut Tree| t.nodes.get_mut(&900).unwrap().window = Some(701),
        |t: &mut Tree| t.nodes.get_mut(&900).unwrap().role = "AXGroup",
        |t: &mut Tree| t.nodes.get_mut(&700).unwrap().role = "AXSheet",
        |t: &mut Tree| t.nodes.get_mut(&700).unwrap().owner = 99,
        |t: &mut Tree| t.nodes.get_mut(&700).unwrap().minimized = Ok(true),
        |t: &mut Tree| t.nodes.get_mut(&900).unwrap().id = "open-panel",
        |t: &mut Tree| t.children_complete = false,
        |t: &mut Tree| t.windows = vec![],
        |t: &mut Tree| t.windows = vec![700, 700],
        |t: &mut Tree| t.focused = 901,
    ] {
        let mut tree = chess_with_host_focus();
        let proof = keyboard_activation_chain(&tree, 42, 900).unwrap();
        alter(&mut tree);
        assert!(!keyboard_activation_matches(&tree, 42, 900, &proof));
    }
    let mut tree = chess_with_host_focus();
    let proof = keyboard_activation_chain(&tree, 42, 900).unwrap();
    // Exhaust the existing finite budget during this revalidation's first
    // parent read, independently of the initial discovery's query cost.
    tree.budget.set(1000);
    tree.relation_reads.set(0);
    tree.expire_on_parent_read = true;
    assert!(
        !keyboard_activation_matches(&tree, 42, 900, &proof),
        "a current proof must not continue by renewing an exhausted budget"
    );
    assert_eq!(tree.relation_reads.get(), 1);
    assert_eq!(tree.budget.get(), 0);
}

#[test]
fn retained_keyboard_revalidation_discovers_once_and_reads_again_at_each_use() {
    for focus in [700, 900] {
        let mut tree = chess_with_host_focus();
        tree.focused = focus;
        let proof = keyboard_activation_chain(&tree, 42, 900).unwrap();
        assert_eq!(
            tree.windows_reads.get(),
            2,
            "initial discovery remains double-proven"
        );
        for _ in 0..2 {
            tree.windows_reads.set(0);
            tree.reads.set(0);
            assert!(keyboard_activation_matches(&tree, 42, 900, &proof));
            assert_eq!(
                tree.windows_reads.get(),
                1,
                "one complete fresh chain per use"
            );
            assert_eq!(
                tree.reads.get(),
                2,
                "fresh selection is still checked twice"
            );
        }
        tree.nodes.get_mut(&700).unwrap().children.clear();
        assert!(
            !keyboard_activation_matches(&tree, 42, 900, &proof),
            "a previous successful use cannot cache a detached relation"
        );
    }
}

#[test]
fn retained_keyboard_revalidation_rejects_a_different_valid_host() {
    let mut tree = chess_with_host_focus();
    tree.focused = 900;
    let proof = keyboard_activation_chain(&tree, 42, 900).unwrap();
    tree.nodes.insert(701, tree.nodes[&700].clone());
    tree.nodes.get_mut(&700).unwrap().children.clear();
    tree.nodes.get_mut(&900).unwrap().parent = Some(701);
    tree.nodes.get_mut(&900).unwrap().window = Some(701);
    tree.windows = vec![700, 701];
    assert!(
        keyboard_activation_chain(&tree, 42, 900).is_some(),
        "the replacement host is independently valid, but is not retained authority"
    );
    assert!(!keyboard_activation_matches(&tree, 42, 900, &proof));
}

#[test]
fn retained_keyboard_revalidation_rejects_edges_changed_during_the_fresh_walk() {
    for fault in [
        RelationFault::Reparented,
        RelationFault::WrongWindow,
        RelationFault::Unreadable,
    ] {
        let mut tree = chess_with_host_focus();
        let proof = keyboard_activation_chain(&tree, 42, 900).unwrap();
        tree.relation_reads.set(0);
        tree.relation_fault = Some(fault);
        assert!(!keyboard_activation_matches(&tree, 42, 900, &proof));
        assert!(
            tree.relation_reads.get() > 1,
            "the first parent read succeeds; a later reciprocal read must reject the change"
        );
    }
}

#[test]
fn retained_keyboard_revalidation_rejects_new_children_and_sibling_selection() {
    let mut tree = chess_with_host_focus();
    tree.focused = 900;
    let proof = keyboard_activation_chain(&tree, 42, 900).unwrap();
    tree.leaf_child_reads.set(0);
    tree.windows_reads.set(0);
    tree.new_child_after_leaf_check = true;
    assert!(!keyboard_activation_matches(&tree, 42, 900, &proof));
    assert_eq!(
        tree.windows_reads.get(),
        1,
        "fresh-chain discovery completes before the final ordinary-leaf check rejects the child"
    );
    assert_eq!(
        tree.focused, 900,
        "unchanged focused ID cannot hide a new child"
    );

    let mut tree = chess_with_host_focus();
    let proof = keyboard_activation_chain(&tree, 42, 900).unwrap();
    tree.host_child_reads.set(0);
    tree.new_sibling_after_selection = true;
    assert!(!keyboard_activation_matches(&tree, 42, 900, &proof));
    assert_eq!(
        tree.host_child_reads.get(),
        2,
        "the fresh chain's final selection rejects the new competing sheet"
    );
}

#[test]
fn retained_keyboard_revalidation_rechecks_identifiers_after_fresh_discovery() {
    for identifier in ["save-panel", "open-panel"] {
        let mut tree = chess_with_host_focus();
        let proof = keyboard_activation_chain(&tree, 42, 900).unwrap();
        tree.identifier_reads.set(0);
        tree.windows_reads.set(0);
        tree.identifier_after_first = Some(identifier);
        assert!(!keyboard_activation_matches(&tree, 42, 900, &proof));
        assert_eq!(tree.windows_reads.get(), 1);
        assert_eq!(
            tree.identifier_reads.get(),
            2,
            "a current file-panel identifier cannot reuse the old ordinary-leaf result"
        );
    }
}

#[test]
fn host_focused_chess_sheet_is_discovered_as_its_own_window() {
    // Chess exposes its new-game sheet as a reciprocal AXChild of the
    // AXFocusedWindow host, with a separate native window omitted from
    // AXWindows. Its buttons must be addressed in that sheet, not the host.
    let tree = chess_with_host_focus();
    assert_eq!(prove(&tree, 42, 900), Some(900));
    assert_eq!(prove_with_visibility(&tree, 42, 900, true), Some(900));
    assert_eq!(
        prove_successor(&tree, 42, 700),
        Some(AttachedSheetSuccessor {
            window_id: 900,
            host_id: 700,
            path: vec![900, 700],
        })
    );
    assert!(prove(&tree, 42, 700).is_none());
    // Discovery must not grant this arbitrary sheet a standard file-dialog
    // foreground lease or substitute its host for the requested target.
    assert!(dialog_host(&tree, 42, 900).is_none());
}

#[test]
fn host_focused_nested_sheet_selects_only_the_unique_leaf() {
    let mut tree = xcode();
    tree.focused = 700;
    assert_eq!(prove(&tree, 42, 950), Some(950));
    assert_eq!(dialog_host(&tree, 42, 950), Some(700));
    assert!(prove(&tree, 42, 900).is_none());
    assert_eq!(
        prove_successor(&tree, 42, 700).unwrap().path,
        [950, 900, 700]
    );
}

#[test]
fn host_focused_sheet_rejects_ambiguous_incomplete_or_changed_selection() {
    let mut tree = chess_with_host_focus();
    tree.children_complete = false;
    assert!(prove(&tree, 42, 900).is_none());

    let mut tree = chess_with_host_focus();
    tree.nodes.insert(901, tree.nodes[&900].clone());
    tree.nodes.get_mut(&700).unwrap().children.push(901);
    assert!(prove(&tree, 42, 900).is_none());
    assert!(prove_successor(&tree, 42, 700).is_none());

    let mut tree = chess_with_host_focus();
    tree.nodes.insert(901, tree.nodes[&900].clone());
    tree.new_sibling_after_selection = true;
    assert!(prove(&tree, 42, 900).is_none());

    let mut tree = chess_with_host_focus();
    tree.change_focus = true;
    assert!(prove(&tree, 42, 900).is_none());
}

#[test]
fn host_focused_sheet_requires_visible_same_process_unminimized_ancestry() {
    for id in [700, 900] {
        let mut tree = chess_with_host_focus();
        tree.nodes.get_mut(&id).unwrap().owner = 99;
        assert!(prove(&tree, 42, 900).is_none());
        let mut tree = chess_with_host_focus();
        tree.nodes.get_mut(&id).unwrap().visible = false;
        assert!(prove(&tree, 42, 900).is_none());
        for minimized in [Ok(true), Err(crate::ax::bindings::kAXErrorCannotComplete)] {
            let mut tree = chess_with_host_focus();
            tree.nodes.get_mut(&id).unwrap().minimized = minimized;
            assert!(prove(&tree, 42, 900).is_none());
        }
    }
    let mut tree = chess_with_host_focus();
    tree.nodes.get_mut(&900).unwrap().window = Some(901);
    assert!(prove(&tree, 42, 900).is_none());
    let mut tree = chess_with_host_focus();
    tree.nodes.get_mut(&900).unwrap().parent = None;
    assert!(prove(&tree, 42, 900).is_none());
}

#[test]
fn host_focused_sheet_never_uses_a_sibling_host_or_incomplete_inventory() {
    for windows in [vec![], vec![700, 700], vec![900]] {
        let mut tree = chess_with_host_focus();
        tree.windows = windows;
        assert!(prove(&tree, 42, 900).is_none());
    }
    let mut tree = chess_with_host_focus();
    let mut sibling = tree.nodes[&700].clone();
    sibling.children.clear();
    tree.nodes.insert(701, sibling);
    tree.windows.push(701);
    tree.focused = 701;
    assert!(prove(&tree, 42, 900).is_none());
    for budget in [0, 2, 5] {
        let tree = chess_with_host_focus();
        tree.budget.set(budget);
        assert!(prove(&tree, 42, 900).is_none());
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
#[test]
fn keyboard_revalidation_diagnostics_distinguish_budget_from_unproven_evidence() {
    let start = std::time::Instant::now();
    let deadline = start + std::time::Duration::from_millis(400);
    assert_eq!(
        super::keyboard_revalidation_diagnostic_status(deadline, deadline, deadline, false),
        "deadline_expired_before_revalidation"
    );
    assert_eq!(
        super::keyboard_revalidation_diagnostic_status(start, deadline, deadline, false),
        "deadline_expired_after_revalidation"
    );
    assert_eq!(
        super::keyboard_revalidation_diagnostic_status(
            start,
            deadline - std::time::Duration::from_micros(1),
            deadline,
            false,
        ),
        "proof_unproven"
    );
}

#[test]
fn keyboard_revalidation_diagnostics_do_not_revoke_an_accepted_proof() {
    let start = std::time::Instant::now();
    let deadline = start + std::time::Duration::from_millis(400);
    // The existing proof's final check can succeed just before expiry while
    // the subsequent diagnostic clock read falls on the boundary.
    assert_eq!(
        super::keyboard_revalidation_diagnostic_status(start, deadline, deadline, true),
        "proven"
    );
}

#[test]
fn exact_focused_nested_leaf_proves_ancestors_missing_from_axwindows() {
    let tree = xcode();
    assert_eq!(tree.windows, [700]);
    assert_eq!(
        prove_focused_sheet_context(&tree, 42, 950, true),
        Some(FocusedSheetContext::ExactLeafAncestors(vec![900, 700]))
    );
    assert!(
        tree.windows_reads.get() >= 2,
        "both complete chain proofs must run"
    );
}

#[test]
fn focused_sheet_context_keeps_successor_priority_and_no_candidate_read_cost() {
    let old = xcode();
    let expected = prove_successor(&old, 42, 700).unwrap();
    let current = xcode();
    assert_eq!(
        prove_focused_sheet_context(&current, 42, 700, true),
        Some(FocusedSheetContext::Successor(expected))
    );
    assert_eq!(current.budget.get(), old.budget.get());
    assert_eq!(current.relation_reads.get(), old.relation_reads.get());
    assert_eq!(current.windows_reads.get(), old.windows_reads.get());
    let old = xcode();
    assert!(prove_successor(&old, 42, 950).is_none());
    let current = xcode();
    assert!(prove_focused_sheet_context(&current, 42, 950, false).is_none());
    assert_eq!(current.budget.get(), old.budget.get());
    assert_eq!(current.reads.get(), old.reads.get());
    assert_eq!(current.windows_reads.get(), 0);
}

#[test]
fn focused_leaf_ancestor_proof_rejects_wrong_focus_children_and_incomplete_reads() {
    for focused in [700, 900] {
        let mut tree = xcode();
        tree.focused = focused;
        assert!(
            prove_focused_leaf_ancestors(&tree, 42, focused).is_none(),
            "a host or parent with a nested child is not the exact focused leaf"
        );
    }
    let tree = xcode();
    assert!(prove_focused_leaf_ancestors(&tree, 42, 900).is_none());
    let mut tree = xcode();
    tree.children_complete = false;
    assert!(prove_focused_leaf_ancestors(&tree, 42, 950).is_none());
    for id in [950, 900] {
        let mut tree = xcode();
        tree.nodes.get_mut(&id).unwrap().window = Some(701);
        assert!(prove_focused_leaf_ancestors(&tree, 42, 950).is_none());
        let mut tree = xcode();
        let parent = tree.nodes[&id].parent.unwrap();
        tree.nodes.get_mut(&parent).unwrap().children.clear();
        assert!(prove_focused_leaf_ancestors(&tree, 42, 950).is_none());
    }
}

#[test]
fn focused_leaf_ancestor_proof_keeps_owner_visibility_and_live_host_guards() {
    for id in [950, 900, 700] {
        let mut tree = xcode();
        tree.nodes.get_mut(&id).unwrap().owner = 99;
        assert!(prove_focused_leaf_ancestors(&tree, 42, 950).is_none());
        let mut tree = xcode();
        tree.nodes.get_mut(&id).unwrap().visible = false;
        assert!(prove_focused_leaf_ancestors(&tree, 42, 950).is_none());
        for state in [Ok(true), Err(crate::ax::bindings::kAXErrorCannotComplete)] {
            let mut tree = xcode();
            tree.nodes.get_mut(&id).unwrap().minimized = state;
            assert!(prove_focused_leaf_ancestors(&tree, 42, 950).is_none());
        }
    }
    for windows in [vec![], vec![700, 700], vec![900]] {
        let mut tree = xcode();
        tree.windows = windows;
        assert!(prove_focused_leaf_ancestors(&tree, 42, 950).is_none());
    }
}

#[test]
fn focused_leaf_ancestor_proof_revalidates_and_never_renews_exhausted_budget() {
    let mut tree = chess_with_host_focus();
    tree.focused = 900;
    tree.new_child_after_leaf_check = true;
    assert!(prove_focused_leaf_ancestors(&tree, 42, 900).is_none());
    assert_eq!(
        tree.leaf_child_reads.get(),
        2,
        "reject child added after first proof"
    );
    let mut tree = xcode();
    tree.change_focus = true;
    assert!(prove_focused_leaf_ancestors(&tree, 42, 950).is_none());
    for fault in [
        RelationFault::Reparented,
        RelationFault::WrongWindow,
        RelationFault::Unreadable,
    ] {
        let mut tree = xcode();
        tree.relation_fault = Some(fault);
        assert!(prove_focused_leaf_ancestors(&tree, 42, 950).is_none());
    }
    let mut tree = xcode();
    tree.expire_on_parent_read = true;
    assert!(prove_focused_sheet_context(&tree, 42, 950, true).is_none());
    assert_eq!(tree.budget.get(), 0);
    let tree = xcode();
    tree.budget.set(0);
    assert!(prove_focused_sheet_context(&tree, 42, 950, true).is_none());
}
