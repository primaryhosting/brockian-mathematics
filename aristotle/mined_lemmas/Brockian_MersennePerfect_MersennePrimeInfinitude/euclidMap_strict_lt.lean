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
import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
# Mersenne Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.MersennePrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The infinitude of Mersenne primes is a famous open problem, so what is established here is a
*Lean-checked reduction*: the statement is shown to be equivalent to the infinitude of even
perfect numbers, via the Euclid–Euler correspondence `p ↦ 2 ^ (p - 1) * (2 ^ p - 1)`.

The target declaration `Brockian.MersennePerfect.MersennePrimeInfinitude` is therefore a
conditional theorem: *if* there are infinitely many even perfect numbers, *then* there are
infinitely many Mersenne primes.  The converse implication, and the resulting equivalence, are
also proved, as is a contrapositive/boundedness reformulation.
-/

namespace Brockian.MersennePerfect

open scoped Nat

/-- The set of exponents `p` for which `2 ^ p - 1` is a (Mersenne) prime.  Such a `p` is
automatically prime itself (see `mersenneExponents_eq`). -/

lemma euclidMap_strict_lt {p q : ℕ} (hp : 1 ≤ p) (hpq : p < q) : euclidMap p < euclidMap q := by
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp).symm⟩
  obtain ⟨b, rfl⟩ : ∃ b, q = b + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  have hab : a < b := by omega
  have h1 : euclidMap (a + 1) < 2 ^ (2 * a + 1) := by
    have hlt : (2 : ℕ) ^ (a + 1) - 1 < 2 ^ (a + 1) := by
      have : (0 : ℕ) < 2 ^ (a + 1) := pow_pos (by norm_num) _
      omega
    calc euclidMap (a + 1) = 2 ^ a * (2 ^ (a + 1) - 1) := by simp [euclidMap]
      _ < 2 ^ a * 2 ^ (a + 1) := by gcongr
      _ = 2 ^ (2 * a + 1) := by ring
  have h2 : (2 : ℕ) ^ (2 * b) ≤ euclidMap (b + 1) := by
    have hb : (2 : ℕ) ^ b ≤ 2 ^ (b + 1) - 1 := by
      have h : (2 : ℕ) ^ (b + 1) = 2 * 2 ^ b := by ring
      have : (1 : ℕ) ≤ 2 ^ b := Nat.one_le_two_pow
      omega
    calc (2 : ℕ) ^ (2 * b) = 2 ^ b * 2 ^ b := by ring
      _ ≤ 2 ^ b * (2 ^ (b + 1) - 1) := Nat.mul_le_mul_left _ hb
      _ = euclidMap (b + 1) := by simp [euclidMap]
  have h3 : (2 : ℕ) ^ (2 * a + 1) ≤ 2 ^ (2 * b) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- `euclidMap` is injective on the set of Mersenne exponents. -/
