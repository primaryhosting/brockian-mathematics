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

lemma cnt_le (i k : ℕ) : G.cnt x i k ≤ k := by
  classical
  unfold cnt
  calc ((Finset.range k).filter (fun v => G.Rch x i v)).card
      ≤ (Finset.range k).card := Finset.card_filter_le _ _
    _ = k := by simp

