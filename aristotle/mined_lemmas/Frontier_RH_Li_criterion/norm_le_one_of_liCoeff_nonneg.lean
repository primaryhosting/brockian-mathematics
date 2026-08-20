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

lemma norm_le_one_of_liCoeff_nonneg {ι : Type*} [Fintype ι] (ρ : ι → ℂ)
    (h : ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoeff ρ n) (i0 : ι) : ‖1 - 1 / ρ i0‖ ≤ 1 := by
  classical
  by_contra hc
  push_neg at hc
  set z : ι → ℂ := fun i => 1 - 1 / ρ i with hz
  set M : ℝ := ‖z i0‖ with hM
  have hM1 : 1 < M := hc
  obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt (2 * (Fintype.card ι : ℝ) + 2) hM1
  obtain ⟨d, hdL, hd⟩ := exists_pow_re_ge_half z (max L 1)
  have hd1 : 1 ≤ d := le_trans (le_max_right L 1) hdL
  have hMd : 2 * (Fintype.card ι : ℝ) + 2 < M ^ d :=
    lt_of_lt_of_le hL (pow_le_pow_right₀ hM1.le (le_trans (le_max_left L 1) hdL))
  have hterm : ∀ i, (1 - z i ^ d).re ≤ 1 - ‖z i‖ ^ d / 2 := by
    intro i
    rw [Complex.sub_re, Complex.one_re]
    linarith [hd i]
  have hsplit : liCoeff ρ d = (1 - z i0 ^ d).re + ∑ i ∈ univ.erase i0, (1 - z i ^ d).re :=
    (Finset.add_sum_erase univ (fun i => (1 - z i ^ d).re) (mem_univ i0)).symm
  have hb1 : (1 - z i0 ^ d).re ≤ 1 - M ^ d / 2 := hterm i0
  have hb2 : ∑ i ∈ univ.erase i0, (1 - z i ^ d).re ≤ (Fintype.card ι : ℝ) := by
    calc ∑ i ∈ univ.erase i0, (1 - z i ^ d).re ≤ ∑ _i ∈ univ.erase i0, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have hnn : (0 : ℝ) ≤ ‖z i‖ ^ d := by positivity
          linarith [hterm i]
      _ = ((univ.erase i0).card : ℝ) := by simp
      _ ≤ (Fintype.card ι : ℝ) := by
          exact_mod_cast Finset.card_le_card (Finset.erase_subset _ _)
  have hpos := h d hd1
  rw [hsplit] at hpos
  linarith

/-- **Li's criterion** (function-theoretic core, finite zero set).

Let `ρ : ι → ℂ` be a finite family of nonzero complex numbers -- the zeros of a completed zeta
function, listed with multiplicity -- which is stable under the functional-equation symmetry
`ρ ↦ 1 - ρ`. Then all the `ρ i` lie on the critical line `Re s = 1/2` (the Riemann hypothesis for
this zero set) if and only if all the Li coefficients
`λ n = ∑ ρ, Re (1 - (1 - 1/ρ) ^ n)` are nonnegative for `n ≥ 1`. -/
