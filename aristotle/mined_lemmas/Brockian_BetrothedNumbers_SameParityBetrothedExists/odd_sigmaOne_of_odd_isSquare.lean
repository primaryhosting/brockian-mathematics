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

theorem odd_sigmaOne_of_odd_isSquare {m : ℕ} (hm : Odd m) (h : IsSquare m) :
    Odd (sigmaOne m) := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [Nat.odd_iff, sigmaOne_mod_two_of_odd hm, ← Nat.odd_iff]
  exact odd_card_divisors_of_factorization_even hm0 (even_factorization_of_isSquare hm0 h)

/-- Every square or twice a square (and nonzero) has odd divisor sum. -/
