import Mathlib

/-!
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory

/-- Cauchy–Schwarz (Hölder with exponents `2, 2`) for continuous, compactly supported
functions on the line. -/

theorem integral_abs_mul_abs_le_sqrt_mul_sqrt (f g : ℝ → ℝ)
    (hf : Continuous f) (hfs : HasCompactSupport f)
    (hg : Continuous g) (hgs : HasCompactSupport g) :
    ∫ t, |f t| * |g t| ≤ Real.sqrt (∫ t, f t ^ 2) * Real.sqrt (∫ t, g t ^ 2) := by
  have hconj : Real.HolderConjugate 2 2 := by constructor <;> norm_num
  have h := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) hconj
    (f := fun t => |f t|) (g := fun t => |g t|)
    (Filter.Eventually.of_forall (fun t => abs_nonneg _))
    (Filter.Eventually.of_forall (fun t => abs_nonneg _))
    ((hf.abs).memLp_of_hasCompactSupport (hfs.abs))
    ((hg.abs).memLp_of_hasCompactSupport (hgs.abs))
  have e1 : ∀ x : ℝ, |x| ^ (2:ℝ) = x ^ 2 := by
    intro x
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  simp_rw [e1] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  convert h using 3

/-- The fundamental theorem of calculus step: the square of a `C¹` compactly supported
function is bounded by the total variation of its square. -/
