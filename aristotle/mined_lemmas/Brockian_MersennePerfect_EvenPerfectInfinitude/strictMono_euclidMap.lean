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

/-
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.MersennePerfect

open ArithmeticFunction Finset
open scoped sigma

/-- The set of even perfect numbers. -/

lemma strictMono_euclidMap : StrictMono euclidMap := by
  apply strictMono_nat_of_lt_succ
  intro k
  have h1 : mersenne (k + 1) < mersenne (k + 1 + 1) := mersenne_lt_mersenne.2 (by omega)
  have h2 : (2:ℕ) ^ k ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 0 < mersenne (k + 1) := mersenne_pos.2 (by omega)
  have : (2:ℕ) ^ k * mersenne (k + 1) < 2 ^ (k + 1) * mersenne (k + 1 + 1) :=
    Nat.mul_lt_mul_of_le_of_lt h2 h1 (by positivity)
  simpa [euclidMap] using this

