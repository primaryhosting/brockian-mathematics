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
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Filter UniqueFactorizationMonoid
open scoped Nat

namespace Brockian.BrocardProblem

/-- The `abc` conjecture, stated for natural numbers, using the radical
`UniqueFactorizationMonoid.radical` (the product of the distinct prime factors):
for every `ε > 0` there is a constant `K > 0` such that whenever `a + b = c` with
`a, b` positive and coprime, we have `c ≤ K * rad(a * b * c) ^ (1 + ε)`. -/

lemma radical_brocard_le (n : ℕ) {m : ℕ} (hm : 0 < m) :
    radical (1 * n ! * m ^ 2) ≤ 4 ^ n * m := by
  have h1 : radical (1 * n ! * m ^ 2) ∣ radical (n !) * radical (m ^ 2) := by
    rw [one_mul]; exact radical_mul_dvd
  rw [radical_pow m two_ne_zero] at h1
  have h2 : radical (1 * n ! * m ^ 2) ≤ radical (n !) * radical m :=
    Nat.le_of_dvd (Nat.mul_pos (Nat.radical_pos _) (Nat.radical_pos _)) h1
  exact h2.trans (Nat.mul_le_mul (radical_factorial_le n) (Nat.radical_le_self_iff.2 hm.ne'))

/-- Overholt's argument: assuming `abc`, every solution of Brocard's problem satisfies
`n ! ≤ C * 4096 ^ n`, with `C` depending only on the `abc` constant for `ε = 1/2`. -/
