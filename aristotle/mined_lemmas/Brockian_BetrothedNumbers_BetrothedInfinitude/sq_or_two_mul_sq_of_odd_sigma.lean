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
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Betrothed (quasi-amicable) numbers

A pair `(m, n)` of distinct positive integers is *betrothed* (or *quasi-amicable*,
or a *reduced amicable pair*) when

  `σ m = σ n = m + n + 1`,

i.e. each of `m` and `n` is the sum of the *nontrivial* proper divisors of the other.
The smallest example is `(48, 75)`.

Whether there are infinitely many betrothed pairs is an open problem, so the target
theorem `BetrothedInfinitude` is stated here as a **Lean-checked conditional
reduction**: infinitude of betrothed pairs follows from a prime-pattern hypothesis
`PrimePatternUnbounded`, which asks for arbitrarily large solutions of a pair of
`σ`-equations in which the two "new" factors are primes.

The hypothesis is *not* vacuous: `isBetrothedPattern_16_25_3_3` exhibits the
solution `(a, b, p, q) = (16, 25, 3, 3)`, which produces the betrothed pair
`(48, 75)`.

Alongside the reduction, several unconditional facts are proved: the first three
betrothed pairs, that no member of a betrothed pair is prime, that both members are
at least `48`, that the set of betrothed pairs is infinite exactly when betrothed
numbers are unbounded, and a parity restriction (in a betrothed pair whose two members
have the same parity, each member is a square or twice a square).
-/

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction

set_option maxRecDepth 100000

/-- `IsBetrothedPair m n` says that `m` and `n` are distinct positive integers with
`σ m = σ n = m + n + 1`; equivalently, each is the sum of the proper divisors of the
other, excluding `1`. -/

theorem sq_or_two_mul_sq_of_odd_sigma :
    ∀ m : ℕ, 0 < m → Odd (sigma 1 m) → ∃ k, m = k ^ 2 ∨ m = 2 * k ^ 2 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hodd
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hm.ne') with h1 | h1
    · exact ⟨1, Or.inl (by omega)⟩
    · set p := m.minFac with hpdef
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hdvd : p ∣ m := Nat.minFac_dvd m
      set e := m.factorization p with hedef
      set c := m / p ^ e with hcdef
      have hsplit : p ^ e * c = m := Nat.ordProj_mul_ordCompl_eq_self m p
      have hcpos : 0 < c := Nat.ordCompl_pos p hm.ne'
      have hcop : Nat.Coprime (p ^ e) c :=
        Nat.Coprime.pow_left e (Nat.coprime_ordCompl hp hm.ne')
      have he1 : 1 ≤ e := Nat.Prime.factorization_pos_of_dvd hp hm.ne' hdvd
      have hclt : c < m := by
        have hpe : 2 ≤ p ^ e := by
          calc 2 ≤ p := hp.two_le
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he1
        nlinarith
      have hsig : sigma 1 m = sigma 1 (p ^ e) * sigma 1 c := by
        rw [← hsplit]
        exact isMultiplicative_sigma.map_mul_of_coprime hcop
      rw [hsig, Nat.odd_mul] at hodd
      obtain ⟨hodd1, hodd2⟩ := hodd
      obtain ⟨k, hk⟩ := ih c hclt hcpos hodd2
      rcases Nat.Prime.eq_two_or_odd hp with hp2 | hpodd
      · have hcodd : ¬ p ∣ c := Nat.not_dvd_ordCompl hp hm.ne'
        rw [hp2] at hcodd
        have hkc : c = k ^ 2 := by
          rcases hk with h | h
          · exact h
          · exact absurd ⟨k ^ 2, h⟩ hcodd
        rcases Nat.even_or_odd e with ⟨t, ht⟩ | ⟨t, ht⟩
        · exact ⟨2 ^ t * k, Or.inl (by rw [← hsplit, hp2, hkc, ht]; ring)⟩
        · exact ⟨2 ^ t * k, Or.inr (by rw [← hsplit, hp2, hkc, ht]; ring)⟩
      · obtain ⟨t, ht⟩ := (odd_sigma_prime_pow_iff hp hpodd).mp hodd1
        rcases hk with h | h
        · exact ⟨p ^ t * k, Or.inl (by rw [← hsplit, h, ht]; ring)⟩
        · exact ⟨p ^ t * k, Or.inr (by rw [← hsplit, h, ht]; ring)⟩

/-- If the two members of a betrothed pair have the same parity, then their common
`σ`-value is odd. -/
