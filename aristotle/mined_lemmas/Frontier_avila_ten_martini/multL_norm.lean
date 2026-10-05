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

theorem multL_norm (v : ℤ → ℂ) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C) (u : Hl2) :
    ‖multL v C hv u‖ ≤ C * ‖u‖ := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hv 0)
  apply lp.norm_le_of_tsum_le (by norm_num) (by positivity)
  have hu := (lp.memℓp u).summable (p := 2) (by norm_num)
  have key : ∀ n : ℤ, ‖(multL v C hv u : ℤ → ℂ) n‖ ^ ((2 : ℝ≥0∞)).toReal
      ≤ C ^ 2 * (‖(u : ℤ → ℂ) n‖ ^ ((2 : ℝ≥0∞)).toReal) := by
    intro n
    rw [multL_apply, norm_mul, rpow_two_eq_sq, rpow_two_eq_sq, mul_pow]
    have h : ‖v n‖ ^ 2 ≤ C ^ 2 := by nlinarith [norm_nonneg (v n), hv n]
    nlinarith [norm_nonneg ((u : ℤ → ℂ) n), sq_nonneg ‖(u : ℤ → ℂ) n‖]
  calc ∑' n : ℤ, ‖(multL v C hv u : ℤ → ℂ) n‖ ^ ((2 : ℝ≥0∞)).toReal
      ≤ ∑' n : ℤ, C ^ 2 * ‖(u : ℤ → ℂ) n‖ ^ ((2 : ℝ≥0∞)).toReal :=
        Summable.tsum_le_tsum key
          (Summable.of_nonneg_of_le (fun n => by positivity) key (hu.mul_left _))
          (hu.mul_left _)
    _ = C ^ 2 * ∑' n : ℤ, ‖(u : ℤ → ℂ) n‖ ^ ((2 : ℝ≥0∞)).toReal := tsum_mul_left
    _ = (C * ‖u‖) ^ ((2 : ℝ≥0∞)).toReal := by
        rw [← lp.norm_rpow_eq_tsum (p := 2) (by norm_num) u, rpow_two_eq_sq, rpow_two_eq_sq,
          mul_pow]

/-- Multiplication by a bounded sequence `v`, as a bounded operator on `ℓ²(ℤ)`. -/
