import Mathlib

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
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

namespace Phys

/-! ## Shannon entropy -/

/-- Shannon entropy (in nats) of a finitely supported weight function. -/

lemma sum_finalJoint_mul_log_prod :
    ∑ x : M × B, finalJoint beta E p U x
        * Real.log (finalMem beta E p U x.1 * gibbs beta E x.2)
      = (∑ m : M, finalMem beta E p U m * Real.log (finalMem beta E p U m))
        + ∑ x : M × B, finalJoint beta E p U x * Real.log (gibbs beta E x.2) := by
  have step : ∀ (m : M) (b : B),
      finalJoint beta E p U (m, b) * Real.log (finalMem beta E p U m * gibbs beta E b)
        = finalJoint beta E p U (m, b) * Real.log (finalMem beta E p U m)
          + finalJoint beta E p U (m, b) * Real.log (gibbs beta E b) := by
    intro m b
    rcases eq_or_lt_of_le (finalMem_nonneg beta E p hp U m) with h0 | h0
    · have hx : finalJoint beta E p U (m, b) = 0 :=
        le_antisymm (by simpa [← h0] using finalJoint_le_finalMem beta E p hp U m b)
          (finalJoint_nonneg beta E p hp U (m, b))
      simp [hx]
    · have : Real.log (finalMem beta E p U m * gibbs beta E b)
          = Real.log (finalMem beta E p U m) + Real.log (gibbs beta E b) :=
        Real.log_mul (ne_of_gt h0) (ne_of_gt (gibbs_pos beta E b))
      rw [this]
      ring
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_congr rfl fun b _ => step m b, Finset.sum_add_distrib, ← Finset.sum_mul]
  rfl

omit [Fintype M] in
