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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open scoped ENNReal

/-! ## The Hilbert space `ℓ²(ℤ, ℝ)` -/

/-- The Hilbert space `ℓ²(ℤ)` (real scalars) on which the almost Mathieu operator acts. -/
abbrev L2Z : Type := lp (fun _ : ℤ => ℝ) 2

/-! ## Multiplication and shift operators on `ℓ²(ℤ)` -/


theorem memlp_mul {g f : ℤ → ℝ} {C : ℝ} (hg : ∀ n, |g n| ≤ C) (hf : Memℓp f 2) :
    Memℓp (fun n => g n * f n) 2 := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hg 0)
  apply memℓp_gen
  have hs := hf.summable (p := 2) (by norm_num)
  have h2 : Summable fun i : ℤ => C ^ (2 : ℝ) * ‖f i‖ ^ (2 : ℝ≥0∞).toReal := hs.mul_left _
  refine h2.of_nonneg_of_le (fun i => by positivity) ?_
  intro i
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, abs_mul]
  rw [Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  gcongr
  exact hg i

