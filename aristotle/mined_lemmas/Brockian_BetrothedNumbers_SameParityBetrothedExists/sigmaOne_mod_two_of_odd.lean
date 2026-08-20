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
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to be the very first command in a file, so the header module
-- docstring above sits immediately after the single `import Mathlib` line.)

namespace Brockian
namespace BetrothedNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/

theorem sigmaOne_mod_two_of_odd {m : ℕ} (hm : Odd m) :
    sigmaOne m % 2 = m.divisors.card % 2 := by
  rw [sigmaOne, Finset.sum_nat_mod]
  have h : ∀ d ∈ m.divisors, d % 2 = 1 := fun d hd =>
    Nat.odd_iff.mp (hm.of_dvd_nat (Nat.mem_divisors.mp hd).1)
  rw [Finset.sum_congr rfl h]
  simp

/-- An odd number with odd divisor sum is a square. -/
