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

lemma insert_isNClique_of_blueN {t : Finset V} {k : ℕ} (hv : v ∈ s) (ht : t ⊆ blueN G s v)
    (hcl : Gᶜ.IsNClique k t) : insert v t ⊆ s ∧ Gᶜ.IsNClique (k + 1) (insert v t) := by
  refine ⟨?_, hcl.insert (fun b hb => ?_)⟩
  · intro x hx
    rcases Finset.mem_insert.1 hx with h | h
    · exact h ▸ hv
    · exact blueN_subset (ht h)
  · have := mem_blueN.1 (ht hb)
    exact (SimpleGraph.compl_adj _ _ _).2 ⟨fun h => this.1.2 h.symm, this.2⟩

/-- The Ramsey property, relative to a fixed graph `G` and localised to subsets. -/
