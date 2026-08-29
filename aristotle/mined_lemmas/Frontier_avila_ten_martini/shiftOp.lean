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


noncomputable def shiftOp (k : ℤ) : L2Z →L[ℝ] L2Z :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun n => (f : ℤ → ℝ) (n + k), memlp_shift k (lp.memℓp f)⟩
      map_add' := by intro f h; ext n; simp
      map_smul' := by intro c f; ext n; simp } 1
    (by
      intro f
      refine lp.norm_le_of_tsum_le (by norm_num) (by positivity) ?_
      have hre : ∑' i : ℤ, ‖(f : ℤ → ℝ) (i + k)‖ ^ (2 : ℝ≥0∞).toReal
          = ∑' i : ℤ, ‖(f : ℤ → ℝ) i‖ ^ (2 : ℝ≥0∞).toReal :=
        (Equiv.addRight k).tsum_eq fun i => ‖(f : ℤ → ℝ) i‖ ^ (2 : ℝ≥0∞).toReal
      calc ∑' i : ℤ, ‖(⟨fun n => (f : ℤ → ℝ) (n + k), memlp_shift k (lp.memℓp f)⟩ : L2Z) i‖
              ^ (2 : ℝ≥0∞).toReal
          = ∑' i : ℤ, ‖(f : ℤ → ℝ) i‖ ^ (2 : ℝ≥0∞).toReal := hre
        _ = ‖f‖ ^ (2 : ℝ≥0∞).toReal := (lp.norm_rpow_eq_tsum (by norm_num) f).symm
        _ ≤ (1 * ‖f‖) ^ (2 : ℝ≥0∞).toReal := by rw [one_mul])

@[simp]
