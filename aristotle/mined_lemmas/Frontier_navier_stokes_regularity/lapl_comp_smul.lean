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

lemma lapl_comp_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E3 → F) (hf : ContDiff ℝ (2 : ℕ) f) (c : ℝ) (x : E3) :
    lapl (fun y => f (c • y)) x = c ^ 2 • lapl f (c • x) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have key : ∀ i : Fin 3, (fun y => partialD i (fun z => f (c • z)) y)
      = fun y => c • partialD i f (c • y) := by
    intro i; funext y; exact partialD_comp_smul f hfd c i y
  simp only [lapl, key, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdi : Differentiable ℝ (fun y => partialD i f y) := differentiable_partialD f hf i
  rw [partialD_const_smul (fun y => partialD i f (c • y)) c i x
      ((hdi (c • x)).comp x ((differentiable_id.const_smul c) x)),
    partialD_comp_smul (fun y => partialD i f y) hdi c i x, smul_smul, sq]

