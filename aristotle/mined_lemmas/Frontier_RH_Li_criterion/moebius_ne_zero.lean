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

theorem moebius_ne_zero {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) : 1 - 1 / ρ ≠ 0 := by
  intro h
  have h2 : (1 : ℂ) = 1 / ρ := sub_eq_zero.1 h
  apply h1
  field_simp at h2
  exact h2

/-- The functional-equation involution `ρ ↦ 1 - ρ` inverts the Möbius image. -/
