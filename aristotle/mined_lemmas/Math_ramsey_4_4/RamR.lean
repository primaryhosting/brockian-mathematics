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

lemma RamR.compl {k l N : ℕ} (h : RamR Gᶜ k l N) : RamR G l k N := by
  intro s hs
  rcases h s hs with ⟨t, hts, ht⟩ | ⟨t, hts, ht⟩
  · exact Or.inr ⟨t, hts, ht⟩
  · rw [compl_compl] at ht
    exact Or.inl ⟨t, hts, ht⟩

/-- `R(2, l) ≤ l`. -/
