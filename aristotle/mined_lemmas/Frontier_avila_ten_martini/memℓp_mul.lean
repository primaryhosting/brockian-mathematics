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


lemma memℓp_mul (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) (f : H2) :
    Memℓp (fun n : ℤ => (v n : ℂ) * (f : ℤ → ℂ) n) 2 := by
  apply memℓp_gen
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hv 0)
  have hs := (lp.memℓp f).summable (p := 2) (by norm_num)
  have h2 : Summable fun n : ℤ => C ^ (2 : ℝ≥0∞).toReal * ‖(f : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal :=
    hs.mul_left _
  refine h2.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  exact Real.rpow_le_rpow (by positivity)
    (by nlinarith [norm_nonneg ((f : ℤ → ℂ) n), hv n]) (by norm_num)

/-- Multiplication by a bounded real sequence, as a linear map on `ℓ²(ℤ, ℂ)`. -/
