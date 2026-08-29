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

theorem re_eq_half_iff_norm_eq_one {ρ : ℂ} (hρ : ρ ≠ 0) :
    ρ.re = 1 / 2 ↔ ‖1 - 1 / ρ‖ = 1 := by
  have hn : ‖ρ‖ ≠ 0 := by simpa using hρ
  have h1 : (1 : ℂ) - 1 / ρ = (ρ - 1) / ρ := by field_simp
  rw [h1, norm_div, div_eq_one_iff_eq hn]
  have key : ‖ρ - 1‖ = ‖ρ‖ ↔ ‖ρ - 1‖ ^ 2 = ‖ρ‖ ^ 2 := by
    constructor
    · intro h; rw [h]
    · intro h; nlinarith [norm_nonneg (ρ - 1), norm_nonneg ρ]
  rw [key, sq_norm_re_im, sq_norm_re_im]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  constructor <;> intro h <;> nlinarith [h]

/-- The Möbius image is nonzero as soon as `ρ ∉ {0, 1}`. -/
