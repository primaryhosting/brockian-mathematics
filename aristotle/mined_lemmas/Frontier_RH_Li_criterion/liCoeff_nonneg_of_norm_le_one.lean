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

lemma liCoeff_nonneg_of_norm_le_one {ι : Type*} [Fintype ι] (ρ : ι → ℂ)
    (h : ∀ i, ‖1 - 1 / ρ i‖ ≤ 1) (n : ℕ) : 0 ≤ liCoeff ρ n := by
  refine Finset.sum_nonneg (fun i _ => ?_)
  rw [Complex.sub_re, Complex.one_re, sub_nonneg]
  calc ((1 - 1 / ρ i) ^ n).re ≤ ‖(1 - 1 / ρ i) ^ n‖ := Complex.re_le_norm _
    _ = ‖1 - 1 / ρ i‖ ^ n := by rw [norm_pow]
    _ ≤ 1 := pow_le_one₀ (norm_nonneg _) (h i)

/-- A simultaneous-recurrence (Dirichlet-type) statement, proved by compactness: for a finite
family of complex numbers there are arbitrarily large exponents `d` for which all the powers
`z i ^ d` point into the right half plane, with `Re (z i ^ d) ≥ ‖z i‖ ^ d / 2`. -/
