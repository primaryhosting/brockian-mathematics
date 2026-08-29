/-
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

open Complex Filter

/-! ## Li coefficients of a finite family of zeros -/

/-- The `n`-th **Li coefficient** attached to a finite multiset `Z` of (candidate) zeros:
`λ_n(Z) = ∑_{ρ ∈ Z} Re (1 - (1 - 1/ρ)^n)`.  This is the standard Bombieri–Lagarias
expression of Li's coefficients as a sum over the zeros. -/

theorem one_sub_mem_nontrivialZeros {s : ℂ} (hs : s ∈ nontrivialZeros) :
    1 - s ∈ nontrivialZeros := by
  obtain ⟨hz, htriv, hne1⟩ := hs
  have hsne : ∀ n : ℕ, s ≠ -(n : ℂ) := nontrivialZeros_ne_neg_nat ⟨hz, htriv, hne1⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [riemannZeta_one_sub hsne hne1, hz, mul_zero]
  · rintro ⟨n, hn⟩
    -- then `s = 2n + 3`, which has real part `≥ 1`, so `ζ s ≠ 0`
    have hs' : s = 2 * (n : ℂ) + 3 := by
      have : s = 1 - (-2 * ((n : ℂ) + 1)) := by rw [← hn]; ring
      rw [this]; ring
    refine riemannZeta_ne_zero_of_one_le_re ?_ hz
    rw [hs']
    simp
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  · intro hcon
    have : s = 0 := by
      have := sub_eq_self.1 (by linear_combination hcon : (1 : ℂ) - s = 1 - 0 + s - s)
      linarith [this]
    exact nontrivialZeros_ne_zero ⟨hz, htriv, hne1⟩ this

/-! ## The main theorem -/

/-- **Li's criterion for the Riemann Hypothesis.**

The Riemann Hypothesis holds if and only if, for every finite family `Z` of nontrivial zeros of
`ζ` that is invariant (with multiplicity) under the functional-equation involution `ρ ↦ 1 - ρ`,
all the Li coefficients `λ_n(Z) = ∑_{ρ ∈ Z} Re (1 - (1 - 1/ρ)^n)`, `n ≥ 1`, are nonnegative. -/
