/-
# Bkt Transition
Category: Frontier Phys
Target: Phys.bkt_transition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Phys

/-- Parameters of the two–dimensional XY model on a disc of radius `R`:
`J` is the spin stiffness (coupling), `kB` Boltzmann's constant and `a` the
short–distance cutoff (lattice spacing / vortex core size). -/
structure XYParams where
  /-- spin stiffness -/
  J : ℝ
  /-- Boltzmann constant -/
  kB : ℝ
  /-- short distance cutoff (core radius) -/
  a : ℝ
  hJ : 0 < J
  hkB : 0 < kB
  ha : 0 < a

/-- Energy of a single vortex (topological defect of winding number `±1`) in a
system of linear size `R`: `E = π J log (R / a)`. -/

theorem bkt_transition (p : XYParams) (R : ℝ) (hR : p.a < R) :
    (∀ T : ℝ, T < T_BKT p → 0 < vortexFreeEnergy p T R) ∧
    vortexFreeEnergy p (T_BKT p) R = 0 ∧
    (∀ T : ℝ, T_BKT p < T → vortexFreeEnergy p T R < 0) ∧
    StrictAnti (fun T : ℝ => vortexFreeEnergy p T R) ∧
    Filter.Tendsto (fun R : ℝ => vortexFreeEnergy p 0 R) Filter.atTop Filter.atTop := by
  have hkB := p.hkB
  have ha := p.ha
  have hJ := p.hJ
  have hL : 0 < Real.log (R / p.a) := log_pos_of_lt p hR
  have hT : ∀ T : ℝ, Real.pi * p.J - 2 * p.kB * T = 2 * p.kB * (T_BKT p - T) := by
    intro T
    have : (2 : ℝ) * p.kB ≠ 0 := by positivity
    rw [T_BKT]
    field_simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T hTlt
    rw [vortexFreeEnergy_eq, hT]
    have : 0 < 2 * p.kB * (T_BKT p - T) := by
      have : 0 < T_BKT p - T := by linarith
      positivity
    positivity
  · rw [vortexFreeEnergy_eq, hT]
    simp
  · intro T hTgt
    rw [vortexFreeEnergy_eq, hT]
    have h1 : 2 * p.kB * (T_BKT p - T) < 0 := by
      have : T_BKT p - T < 0 := by linarith
      exact mul_neg_of_pos_of_neg (by positivity) this
    exact mul_neg_of_neg_of_pos h1 hL
  · intro T₁ T₂ h
    simp only [vortexFreeEnergy_eq, hT]
    have : 2 * p.kB * (T_BKT p - T₂) < 2 * p.kB * (T_BKT p - T₁) := by
      apply mul_lt_mul_of_pos_left (by linarith) (by positivity)
    exact mul_lt_mul_of_pos_right this hL
  · simp only [vortexFreeEnergy_eq, sub_zero, mul_zero]
    have hpi : 0 < Real.pi * p.J := by positivity
    apply Filter.Tendsto.const_mul_atTop hpi
    · -- log (R / a) → ∞
      have h : Filter.Tendsto (fun R : ℝ => R / p.a) Filter.atTop Filter.atTop := by
        simpa using Filter.Tendsto.atTop_div_const ha (f := fun R : ℝ => R) Filter.tendsto_id
      exact Real.tendsto_log_atTop.comp h

end Phys

import Mathlib

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

