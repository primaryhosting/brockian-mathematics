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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian.ZumkellerNumbers

/-- A positive integer `n` is a *Zumkeller number* if its set of divisors can be split into
two parts with equal sums, i.e. there is a set `A` of divisors of `n` whose sum is exactly
half of `σ(n)`. -/

theorem odd_zumkeller_three_primeFactors {n : ℕ} (hodd : Odd n) (hz : IsZumkeller n) :
    3 ≤ n.primeFactors.card := by
  by_contra hc
  push_neg at hc
  have hpos := hz.1
  have hn0 : n ≠ 0 := hpos.ne'
  have habund := zumkeller_two_mul_le_sigma hz
  have hoddp : ∀ p ∈ n.primeFactors, 3 ≤ p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    have h2 := hpp.two_le
    rcases Nat.lt_or_ge p 3 with hlt | hge
    · exfalso
      interval_cases p
      · rw [Nat.odd_iff] at hodd
        obtain ⟨c, rfl⟩ := hdvd
        omega
    · exact hge
  have hsigma : ∑ d ∈ n.divisors, d < 2 * n := by
    have hcases : n.primeFactors.card = 0 ∨ n.primeFactors.card = 1 ∨ n.primeFactors.card = 2 := by
      omega
    rcases hcases with h0 | h1 | h2
    · have hempty : n.primeFactors = ∅ := Finset.card_eq_zero.mp h0
      have hn1 : n = 1 := by
        rcases Nat.primeFactors_eq_empty.mp hempty with h | h
        · exact absurd h hn0
        · exact h
      subst hn1
      simp
    · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
      have hmp : p ∈ n.primeFactors := by rw [hp]; exact Finset.mem_singleton_self p
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hmp
      have hp3 : 3 ≤ p := hoddp p hmp
      have hfac : n = p ^ (n.factorization p) := by
        have h1' := Nat.factorization_prod_pow_eq_self hn0
        rw [Finsupp.prod, Nat.support_factorization, hp, Finset.prod_singleton] at h1'
        exact h1'.symm
      rw [hfac]
      have hlt := two_sigma_lt_three hpp hp3 (n.factorization p)
      have hpe : 0 < p ^ (n.factorization p) := pow_pos (by omega) _
      omega
    · obtain ⟨p, q, hne, hpq⟩ := Finset.card_eq_two.mp h2
      have hmp : p ∈ n.primeFactors := by rw [hpq]; simp
      have hmq : q ∈ n.primeFactors := by rw [hpq]; simp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hmp
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors hmq
      have hp3 : 3 ≤ p := hoddp p hmp
      have hq3 : 3 ≤ q := hoddp q hmq
      have hfac : n = p ^ (n.factorization p) * q ^ (n.factorization q) := by
        have h1' := Nat.factorization_prod_pow_eq_self hn0
        rw [Finsupp.prod, Nat.support_factorization, hpq, Finset.prod_pair hne] at h1'
        exact h1'.symm
      by_cases hp_eq3 : p = 3
      · have hq5 : 5 ≤ q := five_le_of_prime hqp hq3 (by omega)
        rw [hfac]
        exact sigma_lt_two_mul_two_primes hpp hqp hp3 hq5 hne _ _
      · have hp5 : 5 ≤ p := five_le_of_prime hpp hp3 hp_eq3
        rw [hfac, mul_comm]
        exact sigma_lt_two_mul_two_primes hqp hpp hq3 hp5 (Ne.symm hne) _ _
  omega

end Brockian.ZumkellerNumbers

