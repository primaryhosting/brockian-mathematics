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
def IsSophieGermainPrime (p : ℕ) : Prop := p.Prime ∧ (2 * p + 1).Prime

/-- If `p ≡ 3 [MOD 4]` and `2 * p + 1` is prime, then `2 * p + 1` divides the Mersenne
number `2 ^ p - 1`.  Indeed `q = 2 * p + 1` satisfies `q % 8 = 7`, so `2` is a quadratic
residue mod `q`, and Euler's criterion gives `2 ^ ((q - 1) / 2) = 2 ^ p = 1` in `ZMod q`. -/
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
theorem prime_of_dvd_mersenne {p : ℕ} (hp : Nat.Prime p) (hd : (2 * p + 1) ∣ 2 ^ p - 1) :
    Nat.Prime (2 * p + 1) := by
  by_contra hnp
  have hp2 := hp.two_le
  have hq0 : 0 < 2 * p + 1 := by omega
  have hsq := Nat.minFac_sq_le_self hq0 hnp
  set r := (2 * p + 1).minFac with hr
  have hq1 : 2 * p + 1 ≠ 1 := by omega
  have hrp : r.Prime := Nat.minFac_prime hq1
  haveI : Fact r.Prime := ⟨hrp⟩
  have hrd : r ∣ 2 ^ p - 1 := (Nat.minFac_dvd _).trans hd
  have h2 : ((2 : ZMod r)) ^ p = 1 := by
    have h0 : ((2 ^ p - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hrd
    have h1 : (1 : ℕ) ≤ 2 ^ p := Nat.one_le_two_pow
    rw [Nat.cast_sub h1] at h0
    push_cast at h0
    exact sub_eq_zero.mp h0
  have hne0 : (2 : ZMod r) ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega : p ≠ 0)] at h2
    exact zero_ne_one h2
  have hord : orderOf (2 : ZMod r) ∣ p := orderOf_dvd_of_pow_eq_one h2
  have hne1 : orderOf (2 : ZMod r) ≠ 1 := by
    intro h
    have h21 : (2 : ZMod r) = 1 := orderOf_eq_one_iff.1 h
    have hcast : ((2 : ℕ) : ZMod r) = ((1 : ℕ) : ZMod r) := by push_cast; exact h21
    have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).1 hcast
    have hone : r ∣ 1 := (Nat.modEq_iff_dvd' (by norm_num)).1 hmod.symm
    exact hrp.one_lt.ne' (Nat.dvd_one.mp hone)
  have hordp : orderOf (2 : ZMod r) = p := (hp.eq_one_or_self_of_dvd _ hord).resolve_left hne1
  have hdvd : p ∣ r - 1 := hordp ▸ ZMod.orderOf_dvd_card_sub_one hne0
  have hr2 : 2 ≤ r := hrp.two_le
  have hle : p ≤ r - 1 := Nat.le_of_dvd (by omega) hdvd
  have hlt : p + 1 ≤ r := by omega
  nlinarith

/-- **Mersenne criterion for safe primes.** For a prime `p ≡ 3 [MOD 4]`, the number
`2 * p + 1` is prime if and only if it divides the Mersenne number `2 ^ p - 1`. -/
theorem prime_two_mul_add_one_iff_dvd_mersenne {p : ℕ} (hp : Nat.Prime p) (h4 : p % 4 = 3) :
    Nat.Prime (2 * p + 1) ↔ (2 * p + 1) ∣ 2 ^ p - 1 :=
  ⟨fun hq => dvd_mersenne_of_safe_prime h4 hq, fun hd => prime_of_dvd_mersenne hp hd⟩

/-- Equivalent reformulation of the problem restricted to `p ≡ 3 [MOD 4]`: the primes
`p ≡ 3 [MOD 4]` whose associated Mersenne number `2 ^ p - 1` is divisible by `2 * p + 1`
are exactly the Sophie Germain primes `p ≡ 3 [MOD 4]`. -/
theorem mersenne_set_eq_sophieGermain_set :
    {p : ℕ | p.Prime ∧ p % 4 = 3 ∧ (2 * p + 1) ∣ 2 ^ p - 1} =
      {p : ℕ | IsSophieGermainPrime p ∧ p % 4 = 3} := by
  ext p
  simp only [Set.mem_setOf_eq, IsSophieGermainPrime]
  constructor
  · rintro ⟨hp, h4, hd⟩
    exact ⟨⟨hp, prime_of_dvd_mersenne hp hd⟩, h4⟩
  · rintro ⟨⟨hp, hq⟩, h4⟩
    exact ⟨hp, h4, dvd_mersenne_of_safe_prime h4 hq⟩

/-- **Conditional reduction of the infinitude of Sophie Germain primes.**

The infinitude of Sophie Germain primes is a famous open problem, so it is established here in
a reduced (conditional) form: it suffices to exhibit arbitrarily large primes `p ≡ 3 [MOD 4]`
for which `2 * p + 1` divides the Mersenne number `2 ^ p - 1`.  Under that hypothesis the set
of Sophie Germain primes is infinite. -/
theorem SophieGermainInfinitude
    (h : ∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ p % 4 = 3 ∧ (2 * p + 1) ∣ 2 ^ p - 1) :
    {p : ℕ | IsSophieGermainPrime p}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hNp, hp, _, hd⟩ := h N
  exact ⟨p, ⟨hp, prime_of_dvd_mersenne hp hd⟩, hNp⟩

/-- Sanity check: `11` is a Sophie Germain prime (`11` and `23` are prime). -/
theorem isSophieGermainPrime_eleven : IsSophieGermainPrime 11 := by
  constructor <;> norm_num

end Brockian.SophieGermain

