/-
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

noncomputable section

/-! ## The Hilbert space `ℓ²(ℤ, ℂ)` -/

/-- The Hilbert space `ℓ²(ℤ, ℂ)` on which the almost Mathieu operator acts. -/
abbrev H2 := ℓ²(ℤ, ℂ)

instance : Nontrivial H2 := by
  refine ⟨lp.single 2 (0 : ℤ) (1 : ℂ), 0, ?_⟩
  intro h
  have : (lp.single 2 (0 : ℤ) (1 : ℂ) : ℤ → ℂ) 0 = (0 : H2) 0 := by rw [h]
  simp [lp.single_apply] at this

/-! ## Shift operators -/


lemma norm_mulL_le (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) (f : H2) :
    ‖mulL v C hv f‖ ≤ C * ‖f‖ := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hv 0)
  refine lp.norm_le_of_tsum_le (by norm_num) (by positivity) ?_
  have hsum : ∀ n : ℤ, ‖(mulL v C hv f : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal
      ≤ C ^ (2 : ℝ≥0∞).toReal * ‖(f : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal := by
    intro n
    show ‖(v n : ℂ) * (f : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      ← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity)
      (by nlinarith [norm_nonneg ((f : ℤ → ℂ) n), hv n]) (by norm_num)
  have hs := (lp.memℓp f).summable (p := 2) (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  calc ∑' n : ℤ, ‖(mulL v C hv f : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal
      ≤ ∑' n : ℤ, C ^ (2 : ℝ≥0∞).toReal * ‖(f : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal :=
        Summable.tsum_le_tsum hsum ((lp.memℓp (mulL v C hv f)).summable (by norm_num))
          (hs.mul_left _)
    _ = C ^ (2 : ℝ≥0∞).toReal * ∑' n : ℤ, ‖(f : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal := tsum_mul_left
    _ = (C * ‖f‖) ^ (2 : ℝ≥0∞).toReal := by
        rw [Real.mul_rpow hC (norm_nonneg _), lp.norm_rpow_eq_tsum (by norm_num)]

/-- Multiplication by a bounded real sequence, as a bounded operator on `ℓ²(ℤ, ℂ)`. -/
