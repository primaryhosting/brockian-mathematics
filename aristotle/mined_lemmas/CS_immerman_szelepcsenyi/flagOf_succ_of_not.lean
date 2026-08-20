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

lemma flagOf_succ_of_not {i u v : ℕ} (h : ¬ G.Rch x i u) :
    flagOf G x i (u + 1) v = flagOf G x i u v := by
  unfold flagOf
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨y, hy, hy2, hy3⟩
    rcases Nat.lt_or_ge y u with h' | h'
    · exact ⟨y, h', hy2, hy3⟩
    · have : y = u := by omega
      exact absurd (this ▸ hy2) h
  · rintro ⟨y, hy, hy2, hy3⟩
    exact ⟨y, by omega, hy2, hy3⟩

