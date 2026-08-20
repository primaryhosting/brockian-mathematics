import Mathlib

/-!
# Upper bound for the Ramsey number R(4,4)

This file develops, from scratch, the classical inductive bounds on two-colour Ramsey
numbers, culminating in `Math.ramsey_upper_4_4`: every graph on a vertex set of size at
least `18` contains a `4`-clique or an independent set of size `4`.
-/

namespace Math

open Finset

variable {V : Type*} [DecidableEq V]

open scoped Classical in
/-- The neighbours of `v` inside `s` (excluding `v` itself). -/

lemma insert_isNClique_of_redN {t : Finset V} {k : ℕ} (hv : v ∈ s) (ht : t ⊆ redN G s v)
    (hcl : G.IsNClique k t) : insert v t ⊆ s ∧ G.IsNClique (k + 1) (insert v t) := by
  refine ⟨?_, hcl.insert (fun b hb => ?_)⟩
  · intro x hx
    rcases Finset.mem_insert.1 hx with h | h
    · exact h ▸ hv
    · exact redN_subset (ht h)
  · exact (mem_redN.1 (ht hb)).2

/-- Extending a co-clique in the non-neighbourhood of `v` by `v`. -/
