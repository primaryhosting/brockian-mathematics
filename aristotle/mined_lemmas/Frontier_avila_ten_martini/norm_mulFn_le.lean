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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## The Hilbert space `ℓ²(ℤ)` -/

/-- The Hilbert space `ℓ²(ℤ)` on which the almost Mathieu operator acts. -/
abbrev HilbertZ : Type := lp (fun _ : ℤ => ℂ) 2

instance : Nontrivial HilbertZ := by
  refine ⟨lp.single 2 (0 : ℤ) (1 : ℂ), 0, ?_⟩
  intro h
  have := congrArg (fun f : HilbertZ => (f : ℤ → ℂ) 0) h
  simp at this


theorem norm_mulFn_le (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) (f : HilbertZ) :
    ‖mulFn v C hv f‖ ≤ C * ‖f‖ := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hv 0)
  have h2 : (0:ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  refine lp.norm_le_of_tsum_le h2 (by positivity) ?_
  have hle : ∀ n : ℤ, ‖(mulFn v C hv f : ℤ → ℂ) n‖ ^ ((2:ℝ≥0∞).toReal)
      ≤ C ^ (2:ℝ) * ‖(f : ℤ → ℂ) n‖ ^ (2:ℝ) := by
    intro n
    have h1 : ‖(mulFn v C hv f : ℤ → ℂ) n‖ ≤ C * ‖(f : ℤ → ℂ) n‖ := by
      simp only [mulFn_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hv n) (norm_nonneg _)
    calc ‖(mulFn v C hv f : ℤ → ℂ) n‖ ^ ((2:ℝ≥0∞).toReal)
        ≤ (C * ‖(f : ℤ → ℂ) n‖) ^ ((2:ℝ≥0∞).toReal) :=
          Real.rpow_le_rpow (norm_nonneg _) h1 (by norm_num)
      _ = C ^ (2:ℝ) * ‖(f : ℤ → ℂ) n‖ ^ (2:ℝ) := by
          rw [Real.mul_rpow hC (norm_nonneg _)]; norm_num
  have hsum : ∑' n : ℤ, ‖(mulFn v C hv f : ℤ → ℂ) n‖ ^ ((2:ℝ≥0∞).toReal)
      ≤ ∑' n : ℤ, C ^ (2:ℝ) * ‖(f : ℤ → ℂ) n‖ ^ (2:ℝ) := by
    refine Summable.tsum_le_tsum hle ?_ ((summable_sq f).mul_left _)
    have := (lp.memℓp (mulFn v C hv f)).summable (p := 2) (by norm_num)
    simpa using this
  refine hsum.trans ?_
  rw [tsum_mul_left]
  have : ∑' n : ℤ, ‖(f : ℤ → ℂ) n‖ ^ (2:ℝ) = ‖f‖ ^ (2:ℝ) := by
    have := lp.norm_rpow_eq_tsum (p := 2) h2 f
    simpa using this.symm
  rw [this, ← Real.mul_rpow hC (norm_nonneg _)]
  norm_num

/-- Multiplication by a bounded real-valued potential, as a bounded operator on `ℓ²(ℤ)`. -/
