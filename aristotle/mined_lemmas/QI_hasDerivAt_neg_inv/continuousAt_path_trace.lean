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

import Mathlib

/-!
# Scalar integrals used in the integral representations
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace QI


theorem continuousAt_path_trace (hρ : ρ.PosDef) (hσ : σ.PosDef) (A B : Mat n) {p : ℝ × ℝ}
    (ht : 0 ≤ p.1) (h0 : 0 ≤ p.2) (h1 : p.2 ≤ 1) :
    ContinuousAt (fun q : ℝ × ℝ =>
      (A * res (pathState ρ σ q.2) q.1 * B * res (pathState ρ σ q.2) q.1).trace.re) p := by
  have hY : Continuous (fun q : ℝ × ℝ => pathState ρ σ q.2 + (q.1 : ℂ) • (1 : Mat n)) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [pathState, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
      Matrix.one_apply]
    fun_prop
  have hpd : (pathState ρ σ p.2 + (p.1 : ℂ) • 1).PosDef :=
    posDef_shift (pathState_posDef hρ hσ h0 h1) ht
  have hdet : (pathState ρ σ p.2 + (p.1 : ℂ) • 1).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit
    exact this.ne_zero
  have hinvAt : ContinuousAt Inv.inv (pathState ρ σ p.2 + (p.1 : ℂ) • 1) := by
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  have hR : ContinuousAt (fun q : ℝ × ℝ => res (pathState ρ σ q.2) q.1) p := by
    have h := ContinuousAt.comp (g := fun X : Mat n => X⁻¹) (x := p) hinvAt hY.continuousAt
    simpa [Function.comp_def, res] using h
  have hM : ContinuousAt
      (fun q : ℝ × ℝ => A * res (pathState ρ σ q.2) q.1 * B * res (pathState ρ σ q.2) q.1) p :=
    ((continuousAt_const.mul hR).mul continuousAt_const).mul hR
  exact Complex.continuous_re.continuousAt.comp
    ((Continuous.matrix_trace continuous_id).continuousAt.comp hM)

