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
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.SophieGermain

/-- `p` is a *Sophie Germain prime* if both `p` and `2 * p + 1` are prime. -/

theorem dvd_mersenne_of_safe_prime {p : ℕ} (h4 : p % 4 = 3) (hq : Nat.Prime (2 * p + 1)) :
    (2 * p + 1) ∣ 2 ^ p - 1 := by
  haveI : Fact (Nat.Prime (2 * p + 1)) := ⟨hq⟩
  have hq2 : 2 * p + 1 ≠ 2 := by omega
  have h8 : (2 * p + 1) % 8 = 7 := by omega
  have hsquare : IsSquare (2 : ZMod (2 * p + 1)) :=
    (ZMod.exists_sq_eq_two_iff hq2).2 (Or.inr h8)
  have hne0 : (2 : ZMod (2 * p + 1)) ≠ 0 := by
    intro h
    have hcast : ((2 : ℕ) : ZMod (2 * p + 1)) = 0 := by push_cast; exact h
    have hdvd := (ZMod.natCast_eq_zero_iff _ _).1 hcast
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have heuler := (ZMod.euler_criterion (2 * p + 1) hne0).1 hsquare
  have hhalf : (2 * p + 1) / 2 = p := by omega
  rw [hhalf] at heuler
  have h1 : (1 : ℕ) ≤ 2 ^ p := Nat.one_le_two_pow
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1]
  push_cast
  rw [heuler, sub_self]

/-- Converse direction: if `p` is prime and `2 * p + 1` divides `2 ^ p - 1`, then `2 * p + 1`
is prime.  Any prime factor `r` of `2 * p + 1` has `2` of multiplicative order `p` mod `r`,
hence `p ∣ r - 1` and `r ≥ p + 1`; a composite `2 * p + 1` would need `r ^ 2 ≤ 2 * p + 1`. -/
