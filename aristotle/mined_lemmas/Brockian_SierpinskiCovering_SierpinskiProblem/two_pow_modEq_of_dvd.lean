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
# Sierpinski Problem
Category: Brockian Conjecture
Target: Brockian.SierpinskiCovering.SierpinskiProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace Brockian
namespace SierpinskiCovering

/-- The covering table: for a residue `r` of the exponent modulo `36`, this list records a
small prime that divides `78557 * 2 ^ r + 1` (and also divides `2 ^ 36 - 1`, so that the
divisibility only depends on the exponent modulo `36`).

The primes used are `3, 5, 7, 13, 19, 37, 73`, which form the classical covering system
for the Sierpiński number `78557`. -/

lemma two_pow_modEq_of_dvd {p n : ℕ} (hp : p ∣ 2 ^ 36 - 1) :
    (2 : ℕ) ^ n ≡ 2 ^ (n % 36) [MOD p] := by
  have h36 : (2 : ℕ) ^ 36 ≡ 1 [MOD p] :=
    ((Nat.modEq_iff_dvd' (by norm_num)).mpr hp).symm
  calc (2 : ℕ) ^ n = (2 ^ 36) ^ (n / 36) * 2 ^ (n % 36) := by
        rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    _ ≡ 1 ^ (n / 36) * 2 ^ (n % 36) [MOD p] := Nat.ModEq.mul_right _ (h36.pow _)
    _ = 2 ^ (n % 36) := by ring

/-- The covering prime attached to `n` indeed divides `78557 * 2 ^ n + 1`. -/
