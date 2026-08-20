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

lemma cnt_lt_of_not_stab (i : ℕ) (h : ¬ ∀ v, G.Rch x (i + 1) v → G.Rch x i v) :
    G.cnt x i G.N < G.cnt x (i + 1) G.N := by
  classical
  push_neg at h
  obtain ⟨v, hv1, hv2⟩ := h
  unfold cnt
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_range] at hw ⊢
    exact ⟨hw.1, Rch_succ_of hw.2⟩
  · intro hsub
    have hvmem : v ∈ (Finset.range G.N).filter (fun w => G.Rch x (i + 1) w) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨Rch_lt hv1, hv1⟩
    have := hsub hvmem
    simp only [Finset.mem_filter, Finset.mem_range] at this
    exact hv2 this.2

/-- There is a stabilisation point below `N`. -/
