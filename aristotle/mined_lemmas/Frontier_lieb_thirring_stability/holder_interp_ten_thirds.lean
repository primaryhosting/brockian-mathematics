/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

/-! ## The pointwise (Young) inequality underlying stability -/

/-- The Lieb–Thirring stability constant appearing in the bound
`Kc * a ^ (5/3) - t * a ≥ - ltConst Kc * t ^ (5/2)`. -/

lemma holder_interp_ten_thirds (ψ : Space → ℂ) (hc : Continuous ψ) (h2 : HasCompactSupport ψ) :
    ∫ x, ‖ψ x‖ ^ (10 / 3 : ℝ)
      ≤ (∫ x, ‖ψ x‖ ^ 2) ^ (2 / 3 : ℝ) * (∫ x, ‖ψ x‖ ^ 6) ^ (1 / 3 : ℝ) := by
  have hconj : (3 / 2 : ℝ).HolderConjugate 3 := by constructor <;> norm_num
  set f : Space → ℝ := fun x => ‖ψ x‖ ^ (4 / 3 : ℝ) with hf
  set g : Space → ℝ := fun x => ‖ψ x‖ ^ 2 with hg
  have hfc : Continuous f := (hc.norm).rpow_const (fun _ => Or.inr (by norm_num))
  have hgc : Continuous g := (hc.norm).pow 2
  have hfs : HasCompactSupport f := by
    apply HasCompactSupport.comp_left (g := fun t : ℝ => t ^ (4 / 3 : ℝ)) (h2.norm)
    simp [Real.zero_rpow]
  have hgs : HasCompactSupport g := by
    apply HasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (h2.norm)
    simp
  have hfm : MemLp f (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure Space) :=
    hfc.memLp_of_hasCompactSupport hfs
  have hgm : MemLp g (ENNReal.ofReal (3 : ℝ)) (volume : Measure Space) :=
    hgc.memLp_of_hasCompactSupport hgs
  have h := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq hconj hfm hgm
  have e0 : ∀ a : Space, ‖f a‖ * ‖g a‖ = ‖ψ a‖ ^ (10 / 3 : ℝ) := by
    intro a
    have hn : (0 : ℝ) ≤ ‖ψ a‖ := norm_nonneg _
    rw [hf, hg]
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn _),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖ψ a‖ ^ 2)]
    rw [show ((10 : ℝ) / 3) = 4 / 3 + 2 by norm_num, Real.rpow_add' hn (by norm_num)]
    norm_num
  have e1 : ∀ a : Space, ‖f a‖ ^ (3 / 2 : ℝ) = ‖ψ a‖ ^ 2 := by
    intro a
    have hn : (0 : ℝ) ≤ ‖ψ a‖ := norm_nonneg _
    rw [hf]
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn _)]
    rw [← Real.rpow_mul hn]
    norm_num
  have e2 : ∀ a : Space, ‖g a‖ ^ (3 : ℝ) = ‖ψ a‖ ^ 6 := by
    intro a
    rw [hg]
    simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖ψ a‖ ^ 2)]
    rw [show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  simp only [e0, e1, e2] at h
  convert h using 3
  norm_num

/-- **The base case `N = 1` of the Lieb–Thirring kinetic energy inequality.**
For a single normalized `C¹` wave function with compact support,
`∫ ρ^{5/3} ≤ sobolevConst² · ∫ |∇ψ|²`, where `ρ = |ψ|²`. This is proved unconditionally
from the Sobolev inequality and Hölder interpolation. -/
