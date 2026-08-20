/-
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- The binary (`K = 2`) Goldbach property: `n` is a sum of two primes. -/
def GoldbachK2 (n : ℕ) : Prop := ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- Convenience constructor: if `p` and `n - p` are prime and `p ≤ n`, then `n` is a sum of
two primes. -/
theorem goldbachK2_of_sub_prime (n p : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime (n - p))
    (hpn : p ≤ n) : GoldbachK2 n :=
  ⟨p, n - p, hp, hq, by omega⟩

set_option maxHeartbeats 4000000 in
/-- **Goldbach wheel, `K = 2`, modulus `1051`.**
Every even number `n` with `4 ≤ n ≤ 1051` is a sum of two primes. -/
theorem GoldbachWheelK2_1051 :
    ∀ n : ℕ, 4 ≤ n → n ≤ 1051 → Even n → GoldbachK2 n := by
  intro n h4 hub he
  obtain ⟨m, hm⟩ := he
  obtain ⟨k, rfl, hk⟩ : ∃ k, n = 2 * k + 4 ∧ k ≤ 523 := ⟨m - 2, by omega, by omega⟩
  clear hm h4 hub
  interval_cases k <;>
    first
      | ((refine goldbachK2_of_sub_prime _ 3 ?_ ?_ ?_ <;> norm_num); done)
      | ((refine goldbachK2_of_sub_prime _ 5 ?_ ?_ ?_ <;> norm_num); done)
      | ((refine goldbachK2_of_sub_prime _ 7 ?_ ?_ ?_ <;> norm_num); done)
      | ((refine goldbachK2_of_sub_prime _ 11 ?_ ?_ ?_ <;> norm_num); done)
      | ((refine goldbachK2_of_sub_prime _ 13 ?_ ?_ ?_ <;> norm_num); done)
      | ((refine goldbachK2_of_sub_prime _ 17 ?_ ?_ ?_ <;> norm_num); done)
      | ((refine goldbachK2_of_sub_prime _ 19 ?_ ?_ ?_ <;> norm_num); done)
      | ((refine goldbachK2_of_sub_prime _ 23 ?_ ?_ ?_ <;> norm_num); done)
      | ((refine goldbachK2_of_sub_prime _ 29 ?_ ?_ ?_ <;> norm_num); done)
      | ((refine goldbachK2_of_sub_prime _ 31 ?_ ?_ ?_ <;> norm_num); done)
      | ((refine goldbachK2_of_sub_prime _ 37 ?_ ?_ ?_ <;> norm_num); done)
      | ((refine goldbachK2_of_sub_prime _ 41 ?_ ?_ ?_ <;> norm_num); done)
      | ((refine goldbachK2_of_sub_prime _ 43 ?_ ?_ ?_ <;> norm_num); done)
      | ((refine goldbachK2_of_sub_prime _ 47 ?_ ?_ ?_ <;> norm_num); done)
      | ((refine goldbachK2_of_sub_prime _ 53 ?_ ?_ ?_ <;> norm_num); done)
      | ((refine goldbachK2_of_sub_prime _ 59 ?_ ?_ ?_ <;> norm_num); done)
      | ((refine goldbachK2_of_sub_prime _ 61 ?_ ?_ ?_ <;> norm_num); done)
      | ((refine goldbachK2_of_sub_prime _ 67 ?_ ?_ ?_ <;> norm_num); done)
      | ((refine goldbachK2_of_sub_prime _ 71 ?_ ?_ ?_ <;> norm_num); done)
      | ((refine goldbachK2_of_sub_prime _ 73 ?_ ?_ ?_ <;> norm_num); done)
      | ((refine goldbachK2_of_sub_prime _ 79 ?_ ?_ ?_ <;> norm_num); done)
      | ((refine goldbachK2_of_sub_prime _ 83 ?_ ?_ ?_ <;> norm_num); done)
      | ((refine goldbachK2_of_sub_prime _ 89 ?_ ?_ ?_ <;> norm_num); done)
      | ((refine goldbachK2_of_sub_prime _ 97 ?_ ?_ ?_ <;> norm_num); done)
      | (refine goldbachK2_of_sub_prime _ 2 ?_ ?_ ?_ <;> norm_num)

#print axioms Brockian.GoldbachWheelK2_1051

end Brockian

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

