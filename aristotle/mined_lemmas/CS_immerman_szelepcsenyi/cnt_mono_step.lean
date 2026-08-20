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

lemma cnt_mono_step (i : ℕ) : G.cnt x i G.N ≤ G.cnt x (i + 1) G.N := by
  classical
  unfold cnt
  apply Finset.card_le_card
  intro v hv
  simp only [Finset.mem_filter, Finset.mem_range] at hv ⊢
  exact ⟨hv.1, Rch_succ_of hv.2⟩

