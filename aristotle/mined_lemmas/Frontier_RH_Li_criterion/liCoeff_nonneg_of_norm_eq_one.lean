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

theorem liCoeff_nonneg_of_norm_eq_one {Z : Multiset ℂ} (h : ∀ ρ ∈ Z, ‖1 - 1 / ρ‖ = 1) (n : ℕ) :
    0 ≤ liCoeff Z n := by
  apply Multiset.sum_nonneg
  intro x hx
  rw [Multiset.mem_map] at hx
  obtain ⟨ρ, hρ, rfl⟩ := hx
  have hle : ((1 - 1 / ρ) ^ n).re ≤ ‖(1 - 1 / ρ) ^ n‖ := Complex.re_le_norm _
  rw [norm_pow, h ρ hρ, one_pow] at hle
  linarith

/-- **Hard direction.**  If some element of `Z` has a Möbius image of modulus `> 1`, then some
Li coefficient of `Z` is strictly negative. -/
