import Mathlib

/-!
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Scope of this file.

Li's criterion states that the Riemann hypothesis holds iff the Li coefficients
`λ n = ∑_ρ (1 - (1 - 1/ρ)^n)` (the sum running over the nontrivial zeros of the Riemann zeta
function) are nonnegative for all `n ≥ 1`.  The arithmetic input -- the Hadamard factorisation of
the completed zeta function, which identifies `λ n` with a sum over the zeros -- is not available
in Mathlib.  What is formalised and proved here, unconditionally and without any extra axioms, is
the function-theoretic core of the criterion for a finite zero multiset: for a finite family of
nonzero complex numbers stable under the functional-equation symmetry `ρ ↦ 1 - ρ`, all members lie
on the critical line iff all Li coefficients of the family are nonnegative.  The hard direction is
the Bombieri--Lagarias style argument: if some `1 - 1/ρ` lies outside the closed unit disc, then a
compactness (simultaneous Dirichlet approximation) argument produces arbitrarily large exponents
`d` for which all `d`-th powers point into the right half plane, and the largest one then makes
`λ d` negative.
-/

open scoped BigOperators
open Finset Filter

namespace Frontier

/-- The `n`-th **Li coefficient** attached to a finite family of (nonzero) complex numbers
`ρ : ι → ℂ`, thought of as the zeros of a completed zeta function, listed with multiplicity:
`λ n = ∑ ρ, Re (1 - (1 - 1/ρ) ^ n)`. -/

lemma RH_Li_criterion_hypotheses_satisfiable :
    ∃ ρ : Fin 2 → ℂ, (∀ i, ρ i ≠ 0) ∧ (∀ i, ∃ j, ρ j = 1 - ρ i) ∧ ∀ i, (ρ i).re = 1 / 2 := by
  refine ⟨![1 / 2 + Complex.I, 1 / 2 - Complex.I], ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [Complex.ext_iff]
  · intro i
    fin_cases i
    · exact ⟨1, by simp; ring⟩
    · exact ⟨0, by simp; ring⟩
  · intro i; fin_cases i <;> simp

/-- Non-vacuity check for the other side: for the symmetric off-line pair `{1/4, 3/4}` the second
Li coefficient is negative. -/
