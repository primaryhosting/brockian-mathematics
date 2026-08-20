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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

noncomputable section

/-! ## The Hilbert space `ℓ²(ℤ)` -/

/-- The Hilbert space `ℓ²(ℤ, ℂ)` on which the almost Mathieu operator acts. -/
abbrev L2Z := lp (fun _ : ℤ => ℂ) 2

instance : Nontrivial L2Z := by
  refine ⟨lp.single 2 (0 : ℤ) (1 : ℂ), 0, ?_⟩
  intro h
  have h0 : ‖lp.single (E := fun _ : ℤ => ℂ) 2 (0 : ℤ) (1 : ℂ)‖ = 0 := by rw [h]; simp
  rw [lp.norm_single (by norm_num)] at h0
  simp at h0

/-! ## Shift operators -/


theorem norm_multL (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) (u : L2Z) :
    ‖multL v C hv u‖ ≤ C * ‖u‖ := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hv 0)
  refine lp.norm_le_of_tsum_le (by norm_num) (by positivity) ?_
  have hs := (lp.memℓp u).summable (p := 2) (by norm_num)
  have hle : ∀ n : ℤ, ‖(multL v C hv u : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal
      ≤ C ^ (2 : ℝ≥0∞).toReal * ‖(u : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal := by
    intro n
    have h1 : ‖(multL v C hv u : ℤ → ℂ) n‖ = |v n| * ‖(u : ℤ → ℂ) n‖ := by
      rw [multL_apply]; simp [Complex.norm_real]
    have hvn := hv n
    rw [h1, Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
    gcongr
  calc ∑' n, ‖(multL v C hv u : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal
      ≤ ∑' n, C ^ (2 : ℝ≥0∞).toReal * ‖(u : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal := by
        refine Summable.tsum_le_tsum hle ?_ (hs.mul_left _)
        exact (memℓp_mul v C hv u).summable (by norm_num)
    _ = C ^ (2 : ℝ≥0∞).toReal * ‖u‖ ^ (2 : ℝ≥0∞).toReal := by
        rw [hs.tsum_mul_left, ← lp.norm_rpow_eq_tsum (by norm_num)]
    _ = (C * ‖u‖) ^ (2 : ℝ≥0∞).toReal := by
        rw [Real.mul_rpow hC (norm_nonneg _)]

/-- Multiplication by a bounded real sequence, as a bounded operator on `ℓ²(ℤ)`. -/
