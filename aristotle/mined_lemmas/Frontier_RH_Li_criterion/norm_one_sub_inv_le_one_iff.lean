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

lemma norm_one_sub_inv_le_one_iff {ρ : ℂ} (h : ρ ≠ 0) :
    ‖1 - 1 / ρ‖ ≤ 1 ↔ 1 / 2 ≤ ρ.re := by
  have h1 : (1 : ℂ) - 1 / ρ = (ρ - 1) / ρ := by field_simp
  rw [h1, norm_div, div_le_one (by positivity)]
  rw [show ‖ρ - 1‖ ≤ ‖ρ‖ ↔ ‖ρ - 1‖ ^ 2 ≤ ‖ρ‖ ^ 2 from
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).symm]
  have e1 : ‖ρ - 1‖ ^ 2 = (ρ.re - 1) ^ 2 + ρ.im ^ 2 := by
    rw [Complex.sq_norm]; simp [Complex.normSq_apply]; ring
  have e2 : ‖ρ‖ ^ 2 = ρ.re ^ 2 + ρ.im ^ 2 := by
    rw [Complex.sq_norm]; simp [Complex.normSq_apply]; ring
  rw [e1, e2]
  constructor <;> intro h <;> nlinarith

/-- Easy direction: if all the numbers `1 - 1/ρ` lie in the closed unit disc, then every Li
coefficient is nonnegative. -/
