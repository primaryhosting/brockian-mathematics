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

theorem memMult (v : ℤ → ℂ) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C) (u : Hl2) :
    Memℓp (fun n : ℤ => v n * (u : ℤ → ℂ) n) 2 := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hv 0)
  apply memℓp_gen
  have hu := (lp.memℓp u).summable (p := 2) (by norm_num)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hu.mul_left (C ^ 2))
  rw [norm_mul, rpow_two_eq_sq, rpow_two_eq_sq, mul_pow]
  have h : ‖v n‖ ^ 2 ≤ C ^ 2 := by nlinarith [norm_nonneg (v n), hv n]
  nlinarith [norm_nonneg ((u : ℤ → ℂ) n), sq_nonneg ‖(u : ℤ → ℂ) n‖]

/-- Multiplication by a bounded sequence `v`, as a linear map on `ℓ²(ℤ)`. -/
