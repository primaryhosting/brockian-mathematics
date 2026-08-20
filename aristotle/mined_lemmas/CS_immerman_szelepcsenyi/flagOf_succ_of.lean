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

lemma flagOf_succ_of {i u v : ℕ} (h : G.Rch x i u) :
    flagOf G x i (u + 1) v = (flagOf G x i u v || decide (u = v ∨ G.edg x u v)) := by
  unfold flagOf
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.or_eq_true]
  constructor
  · rintro ⟨y, hy, hy2, hy3⟩
    rcases Nat.lt_or_ge y u with h' | h'
    · exact Or.inl ⟨y, h', hy2, hy3⟩
    · have hyu : y = u := by omega
      subst hyu
      exact Or.inr hy3
  · rintro (⟨y, hy, hy2, hy3⟩ | hc)
    · exact ⟨y, by omega, hy2, hy3⟩
    · exact ⟨u, by omega, h, hc⟩

