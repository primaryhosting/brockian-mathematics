/-
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

noncomputable section

/-! ## The Hilbert space `ℓ²(ℤ)` -/

/-- The complex Hilbert space `ℓ²(ℤ)`, on which the almost Mathieu operator acts. -/
abbrev Hl2 := lp (fun _ : ℤ => ℂ) 2

/-- Auxiliary: the real exponent attached to `p = 2`. -/

theorem amoPot_bound (lam alpha theta : ℝ) (n : ℤ) :
    ‖((amoPot lam alpha theta n : ℝ) : ℂ)‖ ≤ 2 * |lam| := by
  rw [Complex.norm_real, amoPot]
  have h := Real.abs_cos_le_one (2 * Real.pi * (theta + n * alpha))
  calc |2 * lam * Real.cos (2 * Real.pi * (theta + n * alpha))|
      = |2 * lam| * |Real.cos (2 * Real.pi * (theta + n * alpha))| := abs_mul _ _
    _ ≤ |2 * lam| * 1 := by
        exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = 2 * |lam| := by rw [mul_one, abs_mul]; simp

/-- The **almost Mathieu operator** `H_{λ,α,θ}` on `ℓ²(ℤ)`:
`(H u)(n) = u(n+1) + u(n-1) + 2 λ cos(2π(θ + nα)) u(n)`. -/
