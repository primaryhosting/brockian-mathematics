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

namespace Brockian

/-- The new wheel modulus `1327` is prime. -/

theorem GoldbachWheelK2_1327 (r : ZMod 1327) (N : ℕ) :
    ∃ p q : ℕ, N < p ∧ N < q ∧ Nat.Prime p ∧ Nat.Prime q ∧
      (p : ZMod 1327) + (q : ZMod 1327) = r := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_add_eq_of_ne_zero_1327 r
  obtain ⟨p, hpN, hp, hpa⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := 1327) (isUnit_iff_ne_zero.mpr ha) N
  obtain ⟨q, hqN, hq, hqb⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := 1327) (isUnit_iff_ne_zero.mpr hb) N
  exact ⟨p, q, hpN, hqN, hp, hq, by rw [hpa, hqb, hab]⟩

/-- Natural-number form of the Goldbach wheel for the modulus `1327`: every residue
`r < 1327` is the residue of a sum of two primes. -/
