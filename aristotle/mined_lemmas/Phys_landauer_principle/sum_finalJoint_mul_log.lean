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

lemma sum_finalJoint_mul_log :
    ∑ x : M × B, finalJoint beta E p U x * Real.log (finalJoint beta E p U x)
      = (∑ m : M, p m * Real.log (p m))
        + ∑ b : B, gibbs beta E b * Real.log (gibbs beta E b) := by
  have h : ∑ x : M × B, finalJoint beta E p U x * Real.log (finalJoint beta E p U x)
      = ∑ x : M × B, initJoint beta E p x * Real.log (initJoint beta E p x) :=
    Equiv.sum_comp U.symm (fun x => initJoint beta E p x * Real.log (initJoint beta E p x))
  have step : ∀ (m : M) (b : B),
      initJoint beta E p (m, b) * Real.log (initJoint beta E p (m, b))
        = p m * Real.log (p m) * gibbs beta E b
          + p m * (gibbs beta E b * Real.log (gibbs beta E b)) := by
    intro m b
    unfold initJoint
    rcases eq_or_lt_of_le (hp m) with h0 | h0
    · simp [← h0]
    · have : Real.log ((p m) * gibbs beta E b)
          = Real.log (p m) + Real.log (gibbs beta E b) :=
        Real.log_mul (ne_of_gt h0) (ne_of_gt (gibbs_pos beta E b))
      simp only [this]
      ring
  rw [h, Fintype.sum_prod_type]
  have inner : ∀ m : M, ∑ b : B,
      initJoint beta E p (m, b) * Real.log (initJoint beta E p (m, b))
        = p m * Real.log (p m) + p m * ∑ b : B, gibbs beta E b * Real.log (gibbs beta E b) := by
    intro m
    rw [Finset.sum_congr rfl fun b _ => step m b, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, gibbs_sum, mul_one]
  rw [Finset.sum_congr rfl fun m _ => inner m, Finset.sum_add_distrib, ← Finset.sum_mul,
    hp1, one_mul]

-- Splitting the cross term of the relative entropy.
include hp in
