import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
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

/-! ## Differential operators on `ℝ³` -/

/-- Three dimensional Euclidean space. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The `i`-th partial derivative of a (vector or scalar valued) field on `ℝ³`. -/

lemma divg_comp_smul (u : E3 → E3) (hu : Differentiable ℝ u) (c : ℝ) (x : E3) :
    divg (fun y => c • u (c • y)) x = c ^ 2 * divg u (c • x) := by
  have hd : ∀ i : Fin 3, partialD i (fun y => c • u (c • y)) x = (c * c) • partialD i u (c • x) := by
    intro i
    rw [partialD_const_smul (fun y => u (c • y)) c i x
      ((hu (c • x)).comp x ((differentiable_id.const_smul c) x)),
      partialD_comp_smul u hu c i x, smul_smul]
  simp only [divg, hd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

