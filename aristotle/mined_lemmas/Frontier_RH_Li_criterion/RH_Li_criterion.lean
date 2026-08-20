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

theorem RH_Li_criterion {ι : Type*} [Fintype ι] (ρ : ι → ℂ)
    (h0 : ∀ i, ρ i ≠ 0) (hsymm : ∀ i, ∃ j, ρ j = 1 - ρ i) :
    (∀ i, (ρ i).re = 1 / 2) ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoeff ρ n := by
  constructor
  · intro hre n _
    refine liCoeff_nonneg_of_norm_le_one ρ (fun i => ?_) n
    exact (norm_one_sub_inv_le_one_iff (h0 i)).2 (by rw [hre i])
  · intro hlam i
    have key : ∀ j, 1 / 2 ≤ (ρ j).re := fun j =>
      (norm_one_sub_inv_le_one_iff (h0 j)).1 (norm_le_one_of_liCoeff_nonneg ρ hlam j)
    obtain ⟨j, hj⟩ := hsymm i
    have h1 : (1 : ℝ) / 2 ≤ (1 - ρ i).re := by rw [← hj]; exact key j
    have h2 : (1 : ℝ) / 2 ≤ (ρ i).re := key i
    simp only [Complex.sub_re, Complex.one_re] at h1
    linarith

/-- Non-vacuity check: the hypotheses of `RH_Li_criterion` are satisfiable, e.g. by the
symmetric pair `1/2 ± i` on the critical line. -/
