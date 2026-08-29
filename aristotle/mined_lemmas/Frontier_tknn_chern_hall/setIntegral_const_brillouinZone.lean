import Mathlib

/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
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

/-- The Brillouin torus, modelled as the fundamental domain `[0, 2π] × [0, 2π]` in `ℝ × ℝ`. -/

lemma setIntegral_const_brillouinZone (v : ℝ) :
    (∫ _k in brillouinZone, v) = (2 * π) ^ 2 * v := by
  have h : (0 : ℝ) ≤ 2 * π - 0 := by simp; positivity
  rw [brillouinZone, MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
    MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, Real.volume_Icc,
    ← ENNReal.ofReal_mul h, ENNReal.toReal_ofReal (by nlinarith)]
  simp only [smul_eq_mul]
  ring

/-- A model band insulator with constant Berry curvature realizing any prescribed Chern
number `n`; this shows the hypotheses of `Frontier.tknn_chern_hall` are non-vacuous. -/
