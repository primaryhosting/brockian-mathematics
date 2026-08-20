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

namespace Math

open Complex ArithmeticFunction

/-- The Möbius function at `10` equals `1`. -/

lemma moebius_ten : moebius 10 = 1 := by
  have h2 : (10 : ℕ) = 2 * 5 := by norm_num
  rw [h2, isMultiplicative_moebius.map_mul_of_coprime (by norm_num)]
  rw [moebius_apply_prime Nat.prime_two, moebius_apply_prime (by norm_num)]
  norm_num

/-- A primitive `10`-th root of unity satisfies `ζ ^ 5 = -1`. -/
