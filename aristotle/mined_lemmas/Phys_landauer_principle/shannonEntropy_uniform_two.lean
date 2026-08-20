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

open scoped BigOperators

namespace Phys

/-- Shannon (Gibbs) entropy, in nats, of a finite probability distribution `p`.
Uses the convention `0 * log 0 = 0`, which holds automatically in Mathlib since
`Real.log 0 = 0`. -/

theorem shannonEntropy_uniform_two :
    shannonEntropy (fun _ : Fin 2 => (1 : ℝ) / 2) = Real.log 2 := by
  unfold shannonEntropy
  rw [Fin.sum_univ_two]
  rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  ring

/-- The entropy of an unbiased bit exceeds that of the erased (deterministic) state
by exactly `log 2` nats. -/
