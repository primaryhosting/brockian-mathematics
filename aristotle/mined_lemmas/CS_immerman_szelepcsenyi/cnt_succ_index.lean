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

lemma cnt_succ_index (i k : ℕ) :
    G.cnt x i (k + 1) = G.cnt x i k + (if G.Rch x i k then 1 else 0) := by
  classical
  unfold cnt
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : G.Rch x i k
  · simp [h, Finset.card_insert_of_notMem]
  · simp [h]

/-- If reachability in `i+1` steps coincides with reachability in `i` steps, it stays so. -/
