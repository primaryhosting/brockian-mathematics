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

lemma flagOf_N {i v : ℕ} : flagOf G x i G.N v = decide (G.Rch x (i + 1) v) := by
  unfold flagOf
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨y, _, hy2, hy3 | hy3⟩
    · exact Rch_succ_of (hy3 ▸ hy2)
    · exact Rch_step hy2 hy3
  · rintro (hv | ⟨y, hy, he⟩)
    · exact ⟨v, Rch_lt hv, hv, Or.inl rfl⟩
    · exact ⟨y, Rch_lt hy, hy, Or.inr he⟩

section Fields

variable (G)

