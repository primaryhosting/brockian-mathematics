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
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

/-- Shannon entropy (in nats) of a finite probability vector `p`. -/

theorem landauer_principle
    (k T Q ΔS_env : ℝ) (hT : 0 < T)
    (hClausius : ΔS_env = Q / T)
    (hSecondLaw :
      0 ≤ k * (shannonEntropy ![(1 : ℝ), 0] - shannonEntropy ![(1 : ℝ) / 2, 1 / 2])
            + ΔS_env) :
    k * T * Real.log 2 ≤ Q := by
  have h := landauer_general k T Q ΔS_env (shannonEntropy ![(1 : ℝ) / 2, 1 / 2])
    (shannonEntropy ![(1 : ℝ), 0]) hT hClausius hSecondLaw
  rwa [shannonEntropy_fair_bit, shannonEntropy_erased_bit, sub_zero] at h

end Phys

