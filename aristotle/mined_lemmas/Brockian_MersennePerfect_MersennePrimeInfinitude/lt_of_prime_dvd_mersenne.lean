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

theorem lt_of_prime_dvd_mersenne {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hdvd : q ∣ 2 ^ p - 1) : p < q := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have h1 : (1 : ℕ) ≤ 2 ^ p := Nat.one_le_two_pow
  have hmod : (2 : ℕ) ^ p ≡ 1 [MOD q] := ((Nat.modEq_iff_dvd' h1).2 hdvd).symm
  have hz : (2 : ZMod q) ^ p = 1 := by
    have h := (ZMod.natCast_eq_natCast_iff _ _ q).2 hmod
    push_cast at h
    exact h
  have h2ne : (2 : ZMod q) ≠ 0 := by
    intro h
    have hdvd2 : q ∣ 2 := by
      have : ((2 : ℕ) : ZMod q) = 0 := by push_cast; exact h
      exact (ZMod.natCast_eq_zero_iff 2 q).1 this
    have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 hdvd2
    subst hq2
    have hpow : (2 : ℕ) ∣ 2 ^ p := dvd_pow_self 2 hp.ne_zero
    omega
  have hord : orderOf (2 : ZMod q) ∣ p := orderOf_dvd_of_pow_eq_one hz
  have hordne : orderOf (2 : ZMod q) ≠ 1 := by
    intro h
    have h21 : (2 : ZMod q) = 1 := orderOf_eq_one_iff.1 h
    have : (1 : ZMod q) = 0 := by linear_combination h21
    exact one_ne_zero this
  have hordp : orderOf (2 : ZMod q) = p := (hp.eq_one_or_self_of_dvd _ hord).resolve_left hordne
  have hfermat : orderOf (2 : ZMod q) ∣ q - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h2ne)
  rw [hordp] at hfermat
  have hq2le : 2 ≤ q := hq.two_le
  have hle : p ≤ q - 1 := Nat.le_of_dvd (by omega) hfermat
  omega

/-- The set of primes dividing some Mersenne number `2 ^ p - 1` with `p` prime. -/
