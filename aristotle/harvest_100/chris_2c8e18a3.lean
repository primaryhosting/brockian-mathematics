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
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CarmichaelKorselt

open Nat

/-- `IsCarmichael n` : `n` is a Carmichael number, i.e. `n` is composite (greater than one and
not prime) and satisfies the conclusion of Fermat's little theorem for every base coprime
to `n`. -/
def IsCarmichael (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ a : ℕ, Nat.Coprime a n → a ^ (n - 1) ≡ 1 [MOD n]

/-- A squarefree number is determined by its prime divisors: if every prime dividing `n`
divides `m ≠ 0`, then `n ∣ m`. -/
theorem dvd_of_squarefree_of_forall_prime_dvd {n m : ℕ} (hn : Squarefree n) (hm : m ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → p ∣ m) : n ∣ m := by
  have hn0 : n ≠ 0 := hn.ne_zero
  rw [← Nat.factorization_le_iff_dvd hn0 hm]
  intro p
  by_cases hp : p.Prime
  · by_cases hpn : p ∣ n
    · have h1 : n.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one hn0).1 hn p
      have h2 : 1 ≤ m.factorization p := hp.factorization_pos_of_dvd hm (h p hp hpn)
      exact le_trans h1 h2
    · simp [Nat.factorization_eq_zero_of_not_dvd hpn]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- **Korselt's criterion** (sufficiency direction): a squarefree composite `n` such that
`p - 1 ∣ n - 1` for every prime `p ∣ n` is a Carmichael number. -/
theorem isCarmichael_of_korselt {n : ℕ} (h1 : 1 < n) (hcomp : ¬ n.Prime) (hsq : Squarefree n)
    (hdvd : ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1)) : IsCarmichael n := by
  refine ⟨h1, hcomp, fun a ha => ?_⟩
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · rw [Nat.coprime_zero_left] at ha; omega
    · exact h
  have hpow : 1 ≤ a ^ (n - 1) := Nat.one_le_pow _ _ ha0
  have key : ∀ p : ℕ, p.Prime → p ∣ n → p ∣ (a ^ (n - 1) - 1) := by
    intro p hp hpn
    have hap : Nat.Coprime a p := Nat.Coprime.coprime_dvd_right hpn ha
    have hfermat : a ^ (p - 1) ≡ 1 [MOD p] := by
      have h := Nat.ModEq.pow_totient hap
      rwa [Nat.totient_prime hp] at h
    obtain ⟨t, ht⟩ := hdvd p hp hpn
    have hmod : a ^ (n - 1) ≡ 1 [MOD p] := by
      rw [ht, pow_mul]
      calc (a ^ (p - 1)) ^ t ≡ 1 ^ t [MOD p] := hfermat.pow t
        _ = 1 := one_pow t
    exact (Nat.modEq_iff_dvd' hpow).1 hmod.symm
  by_cases hone : a ^ (n - 1) = 1
  · rw [hone]
  · have hne : a ^ (n - 1) - 1 ≠ 0 := by omega
    exact ((Nat.modEq_iff_dvd' hpow).2
      (dvd_of_squarefree_of_forall_prime_dvd hsq hne key)).symm

section ThreePrimes

variable {p q r : ℕ}

/-- The prime divisors of a product of three distinct primes. -/
theorem prime_dvd_three_primes (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) {s : ℕ}
    (hs : s.Prime) (hdvd : s ∣ p * q * r) : s = p ∨ s = q ∨ s = r := by
  rcases (Nat.Prime.dvd_mul hs).1 hdvd with h | h
  · rcases (Nat.Prime.dvd_mul hs).1 h with h' | h'
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hs hp).1 h')
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hs hq).1 h'))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hs hr).1 h))

/-- A product of three distinct primes is squarefree. -/
theorem squarefree_three_primes (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) : Squarefree (p * q * r) := by
  have hcpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have hcpr : Nat.Coprime p r := (Nat.coprime_primes hp hr).2 hpr
  have hcqr : Nat.Coprime q r := (Nat.coprime_primes hq hr).2 hqr
  refine Nat.squarefree_mul_iff.2 ⟨Nat.Coprime.mul_left hcpr hcqr, ?_, hr.squarefree⟩
  exact Nat.squarefree_mul_iff.2 ⟨hcpq, hp.squarefree, hq.squarefree⟩

/-- A product of three distinct primes has exactly three prime factors. -/
theorem card_primeFactors_three_primes (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) : (p * q * r).primeFactors.card = 3 := by
  have hpf : (p * q * r).primeFactors = {p, q, r} := by
    rw [Nat.primeFactors_mul (Nat.mul_ne_zero hp.pos.ne' hq.pos.ne') hr.pos.ne',
      Nat.primeFactors_mul hp.pos.ne' hq.pos.ne', hp.primeFactors, hq.primeFactors,
      hr.primeFactors]
    ext x; simp [or_assoc]
  rw [hpf]
  rw [Finset.card_insert_of_notMem (by simp [hpq, hpr]),
    Finset.card_insert_of_notMem (by simpa using hqr), Finset.card_singleton]

/-- Korselt's criterion for a product of three distinct primes. -/
theorem isCarmichael_three_primes (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (h1 : (p - 1) ∣ (p * q * r - 1)) (h2 : (q - 1) ∣ (p * q * r - 1))
    (h3 : (r - 1) ∣ (p * q * r - 1)) :
    IsCarmichael (p * q * r) ∧ (p * q * r).primeFactors.card = 3 := by
  refine ⟨isCarmichael_of_korselt ?_ ?_ (squarefree_three_primes hp hq hr hpq hpr hqr) ?_,
    card_primeFactors_three_primes hp hq hr hpq hpr hqr⟩
  · have := hp.two_le; have := hq.two_le; have := hr.two_le
    calc 1 < 2 * 2 * 2 := by norm_num
      _ ≤ p * q * r := by
          exact Nat.mul_le_mul (Nat.mul_le_mul ‹2 ≤ p› ‹2 ≤ q›) ‹2 ≤ r›
  · refine Nat.not_prime_mul ?_ hr.ne_one
    have := hp.two_le; have := hq.two_le
    nlinarith
  · intro s hs hsdvd
    rcases prime_dvd_three_primes hp hq hr hs hsdvd with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3

end ThreePrimes

/-- The Carmichael number `1729 = 7 * 13 * 19`, with exactly three prime factors. -/
theorem isCarmichael_1729 : IsCarmichael 1729 ∧ (1729 : ℕ).primeFactors.card = 3 := by
  have h : (1729 : ℕ) = 7 * 13 * 19 := by norm_num
  rw [h]
  exact isCarmichael_three_primes (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Chernick's construction**: if `6k+1`, `12k+1` and `18k+1` are all prime (`k ≥ 1`), then
their product is a Carmichael number with exactly three prime factors. -/
theorem chernick_isCarmichael {k : ℕ} (hk : 0 < k) (h1 : (6 * k + 1).Prime)
    (h2 : (12 * k + 1).Prime) (h3 : (18 * k + 1).Prime) :
    IsCarmichael ((6 * k + 1) * (12 * k + 1) * (18 * k + 1)) ∧
      ((6 * k + 1) * (12 * k + 1) * (18 * k + 1)).primeFactors.card = 3 := by
  have hprod : (6 * k + 1) * (12 * k + 1) * (18 * k + 1)
      = 36 * k * (36 * k ^ 2 + 15 * k + 2) + 1 := by ring
  have hsub : (6 * k + 1) * (12 * k + 1) * (18 * k + 1) - 1
      = 36 * k * (36 * k ^ 2 + 15 * k + 2) := by rw [hprod]; simp
  have e1 : 6 * k + 1 - 1 = 6 * k := by omega
  have e2 : 12 * k + 1 - 1 = 12 * k := by omega
  have e3 : 18 * k + 1 - 1 = 18 * k := by omega
  refine isCarmichael_three_primes h1 h2 h3 (by omega) (by omega) (by omega) ?_ ?_ ?_
  · rw [hsub, e1]; exact ⟨6 * (36 * k ^ 2 + 15 * k + 2), by ring⟩
  · rw [hsub, e2]; exact ⟨3 * (36 * k ^ 2 + 15 * k + 2), by ring⟩
  · rw [hsub, e3]; exact ⟨2 * (36 * k ^ 2 + 15 * k + 2), by ring⟩

/-- The (open) hypothesis that Chernick's construction produces infinitely many triples:
there are arbitrarily large `k` with `6k+1`, `12k+1`, `18k+1` all prime.  This is a special
case of Dickson's conjecture / the prime `k`-tuples conjecture. -/
def ChernickTriplesInfinite : Prop :=
  ∀ N : ℕ, ∃ k > N, (6 * k + 1).Prime ∧ (12 * k + 1).Prime ∧ (18 * k + 1).Prime

/-- **Conditional reduction of the three-prime Carmichael infinitude problem.**
If Chernick's construction admits infinitely many admissible `k` (a special case of Dickson's
conjecture), then there are infinitely many Carmichael numbers with exactly three prime
factors. -/
theorem ThreePrimeCarmichaelInfinitude (h : ChernickTriplesInfinite) :
    {n : ℕ | IsCarmichael n ∧ n.primeFactors.card = 3}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨k, hkN, h1, h2, h3⟩ := h N
  refine ⟨(6 * k + 1) * (12 * k + 1) * (18 * k + 1), chernick_isCarmichael (by omega) h1 h2 h3, ?_⟩
  have hle : 6 * k + 1 ≤ (6 * k + 1) * (12 * k + 1) * (18 * k + 1) := by
    calc 6 * k + 1 ≤ (6 * k + 1) * (12 * k + 1) := Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ (6 * k + 1) * (12 * k + 1) * (18 * k + 1) := Nat.le_mul_of_pos_right _ (by omega)
  omega

end Brockian.CarmichaelKorselt

