/// Variable Move-To-Front (VMTF) doubly-linked list.
///
/// Variables are ordered by recency of their last bump in a conflict clause.
/// Bumping a variable moves it to the front of the list in O(1).
/// `front_unassigned` walks from the front to find the next branch candidate.
///
/// Used in Focus mode as an O(1)-update alternative to the VSIDS heap.
/// Node 0 is the sentinel (both the "prev of head" and "next of tail").
pub struct VmtfList {
    /// next[0] = front variable (most recently bumped); next[v] = successor of v.
    next: Vec<u32>,
    /// prev[0] = back variable (least recently bumped); prev[v] = predecessor of v.
    prev: Vec<u32>,
}

impl VmtfList {
    /// Build an initial list 1 → 2 → … → n_vars (arbitrary order; VSIDS bumps
    /// will reorder quickly after the first few conflicts).
    pub fn new(n_vars: u32) -> Self {
        let cap = (n_vars + 1) as usize;
        let mut next = vec![0u32; cap];
        let mut prev = vec![0u32; cap];
        if n_vars == 0 {
            return VmtfList { next, prev };
        }
        // sentinel(0) ↔ 1 ↔ 2 ↔ … ↔ n_vars ↔ sentinel(0)
        next[0] = 1;
        prev[0] = n_vars;
        prev[1] = 0;
        for v in 1..n_vars {
            next[v as usize] = v + 1;
            prev[(v + 1) as usize] = v;
        }
        next[n_vars as usize] = 0;
        VmtfList { next, prev }
    }

    /// Move `var` to the front of the list in O(1).
    #[inline]
    pub fn move_to_front(&mut self, var: u32) {
        let front = self.next[0];
        if front == var {
            return; // Already at front.
        }
        // Detach var from its current position.
        let p = self.prev[var as usize];
        let n = self.next[var as usize];
        self.next[p as usize] = n;
        self.prev[n as usize] = p;
        // Insert var at the front.
        self.next[0] = var;
        self.prev[var as usize] = 0;
        self.next[var as usize] = front;
        self.prev[front as usize] = var;
    }

    /// Return the first unassigned variable walking from the front.
    /// Returns `None` if all variables are assigned (search complete).
    #[inline]
    pub fn front_unassigned(&self, is_unassigned: impl Fn(u32) -> bool) -> Option<u32> {
        let mut v = self.next[0];
        while v != 0 {
            if is_unassigned(v) {
                return Some(v);
            }
            v = self.next[v as usize];
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn initial_order_and_move_to_front() {
        let mut vmtf = VmtfList::new(5);
        // Initial order: 1 2 3 4 5
        assert_eq!(vmtf.next[0], 1);
        assert_eq!(vmtf.next[1], 2);
        assert_eq!(vmtf.next[5], 0);

        // Move 3 to front → 3 1 2 4 5
        vmtf.move_to_front(3);
        assert_eq!(vmtf.next[0], 3);
        assert_eq!(vmtf.next[3], 1);
        assert_eq!(vmtf.next[1], 2);
        assert_eq!(vmtf.next[2], 4);

        // Move 3 again (already front): no change
        vmtf.move_to_front(3);
        assert_eq!(vmtf.next[0], 3);
        assert_eq!(vmtf.next[3], 1);

        // Move last element (5) to front → 5 3 1 2 4
        vmtf.move_to_front(5);
        assert_eq!(vmtf.next[0], 5);
        assert_eq!(vmtf.next[5], 3);
        assert_eq!(vmtf.next[4], 0); // 4 is now last
        assert_eq!(vmtf.prev[0], 4);
    }

    #[test]
    fn front_unassigned_skips_assigned() {
        let vmtf = VmtfList::new(4);
        // Vars 1 and 2 assigned; 3 and 4 free
        let result = vmtf.front_unassigned(|v| v > 2);
        assert_eq!(result, Some(3));
    }
}
