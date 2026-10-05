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

theorem shannonEntropy_bit_le_log_two (p : Fin 2 → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) : shannonEntropy p ≤ Real.log 2 := by
  simpa using shannonEntropy_le_log_card p hp hsum

/--
**Landauer's principle, general form.**

A system whose thermodynamic entropy is `k * S_init` before a process and `k * S_final`
after it releases heat `Q` into a reservoir at temperature `T > 0`.  Clausius' relation
gives the reservoir entropy change `ΔS_env = Q / T`, and the second law says the total
entropy change is nonnegative.  Then `Q ≥ k * T * (S_init - S_final)`: any decrease of
the system's information entropy must be paid for with dissipated heat.
-/
