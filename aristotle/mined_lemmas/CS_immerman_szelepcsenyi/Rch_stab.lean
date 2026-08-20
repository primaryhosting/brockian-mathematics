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

lemma Rch_stab (i : ℕ) (h : ∀ v, G.Rch x (i + 1) v → G.Rch x i v) :
    ∀ j v, i ≤ j → G.Rch x j v → G.Rch x i v := by
  intro j
  induction j with
  | zero => intro v hij hv; interval_cases i; exact hv
  | succ j ih =>
      intro v hij hv
      rcases Nat.lt_or_ge i (j + 1) with h' | h'
      · have hij' : i ≤ j := by omega
        rcases hv with hv | ⟨u, hu, he⟩
        · exact ih v hij' hv
        · exact h v (Rch_step (ih u hij' hu) he)
      · have : i = j + 1 := by omega
        subst this; exact hv

