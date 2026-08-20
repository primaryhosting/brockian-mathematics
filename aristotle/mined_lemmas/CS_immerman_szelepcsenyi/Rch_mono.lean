import RequestProject.Counting

/-!
# Soundness of the counting machine

We define an invariant of the states of the counting machine which is satisfied by the
initial state and preserved by every transition, and which guarantees, in the accepting
phase, that no accepting vertex is reachable.
-/

open scoped Classical

namespace CS
namespace IS

open Data

variable (G : Data) (x : List Bool)

/-- The invariant of the inner loop: the vertices counted so far form a set `S` of vertices
`< u` reachable in `i` steps, and the flag correctly records whether one of them witnesses
the reachability of `v` in `i+1` steps. -/

lemma Rch_mono {i j v : ℕ} (hij : i ≤ j) (h : G.Rch x i v) : G.Rch x j v := by
  induction j with
  | zero =>
      have hi : i = 0 := by omega
      subst hi; exact h
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h' | h'
      · exact Rch_succ_of (ih (by omega))
      · have : i = j + 1 := by omega
        subst this; exact h

