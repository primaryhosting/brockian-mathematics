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

/-!
# Sierpinski Problem
Category: Brockian Conjecture
Target: Brockian.SierpinskiCovering.SierpinskiProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian
namespace SierpinskiCovering

/-- A *Sierpiński number* is an odd natural number `k` such that `k * 2 ^ n + 1` is composite
(never prime) for every `n ≥ 1`. -/

theorem dvd_of_covering (p r q : ℕ) (hp : p ∣ 2 ^ 36 - 1)
    (hd : p ∣ 78557 * 2 ^ r + 1) :
    p ∣ 78557 * 2 ^ (36 * q + r) + 1 := by
  have h1 : (2 : ℕ) ^ 36 ≡ 1 [MOD p] :=
    (((Nat.modEq_iff_dvd' (by norm_num)).2 hp)).symm
  have h2 : ((2 : ℕ) ^ 36) ^ q ≡ 1 [MOD p] := by
    simpa using h1.pow q
  have h3 : 78557 * 2 ^ (36 * q + r) + 1 ≡ 78557 * 2 ^ r + 1 [MOD p] := by
    have hpow : (2 : ℕ) ^ (36 * q + r) = ((2 : ℕ) ^ 36) ^ q * 2 ^ r := by
      rw [pow_add, pow_mul]
    rw [hpow]
    have := ((h2.mul_right (2 ^ r)).mul_left 78557).add_right 1
    simpa using this
  exact (Nat.modEq_zero_iff_dvd).1 (h3.trans ((Nat.modEq_zero_iff_dvd).2 hd))

/-- The covering table: for every residue `r < 36` there is a prime in `coveringPrimes`
dividing both `2 ^ 36 - 1` and `78557 * 2 ^ r + 1`. -/
