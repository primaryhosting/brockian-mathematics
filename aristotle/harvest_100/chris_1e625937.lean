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
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.CarmichaelKorselt

/-- Korselt's criterion, used here as the definition of a Carmichael number:
`n` is composite (`1 < n` and not prime), squarefree, and `p - 1 ∣ n - 1`
for every prime `p` dividing `n`. -/
def IsCarmichael (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ Squarefree n ∧ ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1)

/-- `n` is a Carmichael number that is a product of exactly three distinct primes. -/
def IsThreePrimeCarmichael (n : ℕ) : Prop :=
  IsCarmichael n ∧ ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p < q ∧ q < r ∧ n = p * q * r

/-- Korselt's criterion implies the Fermat property: a Carmichael number `n` in the above
sense satisfies `a ^ n ≡ a [MOD n]` for every base `a`.  This justifies the definition. -/
theorem IsCarmichael.fermat {n : ℕ} (h : IsCarmichael n) (a : ℕ) : a ^ n ≡ a [MOD n] := by
  obtain ⟨hn1, -, hsf, hkor⟩ := h
  have hle : a ≤ a ^ n := Nat.le_self_pow (by omega) a
  have key : ∀ p ∈ n.primeFactors, p ∣ a ^ n - a := by
    intro p hpmem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hpd : p ∣ n := Nat.dvd_of_mem_primeFactors hpmem
    have hmod : a ^ n ≡ a [MOD p] := by
      by_cases hpa : p ∣ a
      · have h0 : a ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).2 hpa
        calc a ^ n ≡ 0 ^ n [MOD p] := h0.pow n
          _ = 0 := zero_pow (by omega)
          _ ≡ a [MOD p] := h0.symm
      · have hcop : Nat.Coprime a p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpa).symm
        obtain ⟨m, hm⟩ := hkor p hp hpd
        have hfermat : a ^ (n - 1) ≡ 1 [MOD p] := by
          have ht := Nat.ModEq.pow_totient hcop
          rw [Nat.totient_prime hp] at ht
          calc a ^ (n - 1) = (a ^ (p - 1)) ^ m := by rw [hm, pow_mul]
            _ ≡ 1 ^ m [MOD p] := ht.pow m
            _ = 1 := one_pow m
        calc a ^ n = a ^ (n - 1) * a := by
              rw [← pow_succ]; congr 1; omega
          _ ≡ 1 * a [MOD p] := hfermat.mul_right a
          _ = a := one_mul a
    exact (Nat.modEq_iff_dvd' hle).1 hmod.symm
  have hprod := Finset.prod_primes_dvd (a ^ n - a)
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) key
  rw [Nat.prod_primeFactors_of_squarefree hsf] at hprod
  exact ((Nat.modEq_iff_dvd' hle).2 hprod).symm

/-- Chernick's construction: if `6k+1`, `12k+1`, `18k+1` are all prime (with `k ≥ 1`),
then their product is a Carmichael number with exactly three prime factors. -/
theorem isThreePrimeCarmichael_chernick {k : ℕ} (hk : 1 ≤ k)
    (h1 : Nat.Prime (6 * k + 1)) (h2 : Nat.Prime (12 * k + 1))
    (h3 : Nat.Prime (18 * k + 1)) :
    IsThreePrimeCarmichael ((6 * k + 1) * (12 * k + 1) * (18 * k + 1)) := by
  set p := 6 * k + 1 with hp
  set q := 12 * k + 1 with hq
  set r := 18 * k + 1 with hr
  have hpq : p < q := by omega
  have hqr : q < r := by omega
  have hpr : p < r := by omega
  -- the key arithmetic identity
  have hval : p * q * r = 1296 * k ^ 3 + 396 * k ^ 2 + 36 * k + 1 := by
    simp only [hp, hq, hr]; ring
  have hcube : 1 ≤ k ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hn1 : 1 < p * q * r := by rw [hval]; omega
  have hsub : p * q * r - 1 = 36 * k * (36 * k ^ 2 + 11 * k + 1) := by
    rw [hval]; ring_nf; omega
  refine ⟨⟨hn1, ?_, ?_, ?_⟩, p, q, r, h1, h2, h3, hpq, hqr, rfl⟩
  · -- not prime
    intro hprime
    have hdvd : p ∣ p * q * r := ⟨q * r, by ring⟩
    rcases (Nat.Prime.eq_one_or_self_of_dvd hprime p hdvd) with h | h
    · exact h1.one_lt.ne' h
    · nlinarith [h1.two_le, h2.two_le, h3.two_le]
  · -- squarefree
    have hcpq : Nat.Coprime p q :=
      (Nat.coprime_primes h1 h2).2 hpq.ne
    have hcpr : Nat.Coprime p r :=
      (Nat.coprime_primes h1 h3).2 hpr.ne
    have hcqr : Nat.Coprime q r :=
      (Nat.coprime_primes h2 h3).2 hqr.ne
    rw [Nat.squarefree_mul_iff]
    refine ⟨Nat.Coprime.mul_left hcpr hcqr, ?_, h3.squarefree⟩
    rw [Nat.squarefree_mul_iff]
    exact ⟨hcpq, h1.squarefree, h2.squarefree⟩
  · -- Korselt divisibility
    intro s hs hsdvd
    have hcases : s = p ∨ s = q ∨ s = r := by
      rcases (Nat.Prime.dvd_mul hs).1 hsdvd with h | h
      · rcases (Nat.Prime.dvd_mul hs).1 h with h' | h'
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hs h1).1 h')
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hs h2).1 h'))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hs h3).1 h))
    rw [hsub]
    rcases hcases with h | h | h
    · have hs1 : s - 1 = 6 * k := by omega
      rw [hs1]
      exact ⟨6 * (36 * k ^ 2 + 11 * k + 1), by ring⟩
    · have hs1 : s - 1 = 12 * k := by omega
      rw [hs1]
      exact ⟨3 * (36 * k ^ 2 + 11 * k + 1), by ring⟩
    · have hs1 : s - 1 = 18 * k := by omega
      rw [hs1]
      exact ⟨2 * (36 * k ^ 2 + 11 * k + 1), by ring⟩

/-- The smallest Chernick number, `1729 = 7 * 13 * 19`, is a three-prime Carmichael number. -/
theorem isThreePrimeCarmichael_1729 : IsThreePrimeCarmichael 1729 := by
  have h := isThreePrimeCarmichael_chernick (k := 1) le_rfl (by norm_num) (by norm_num)
    (by norm_num)
  norm_num at h
  exact h

/-- **Conditional infinitude of three-prime Carmichael numbers.**

The unconditional infinitude of Carmichael numbers with exactly three prime factors is an
open problem, so this is a Lean-checked *conditional reduction*: it derives the infinitude
from the (conjectural, a special case of Dickson's conjecture) hypothesis that the linear
forms `6k+1, 12k+1, 18k+1` are simultaneously prime infinitely often.  The construction is
Chernick's, and the Carmichael property is verified through Korselt's criterion. -/
theorem ThreePrimeCarmichaelInfinitude
    (hDickson : ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ Nat.Prime (6 * k + 1) ∧ Nat.Prime (12 * k + 1) ∧
      Nat.Prime (18 * k + 1)) :
    ∀ N : ℕ, ∃ n : ℕ, N < n ∧ IsThreePrimeCarmichael n := by
  intro N
  obtain ⟨k, hkN, h1, h2, h3⟩ := hDickson (N + 1)
  refine ⟨(6 * k + 1) * (12 * k + 1) * (18 * k + 1), ?_,
    isThreePrimeCarmichael_chernick (by omega) h1 h2 h3⟩
  have e1 : 6 * k + 1 ≤ (6 * k + 1) * (12 * k + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have e2 : (6 * k + 1) * (12 * k + 1) ≤ (6 * k + 1) * (12 * k + 1) * (18 * k + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- The set of three-prime Carmichael numbers is infinite, conditionally on the same
Dickson-type hypothesis. -/
theorem setOf_threePrimeCarmichael_infinite
    (hDickson : ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ Nat.Prime (6 * k + 1) ∧ Nat.Prime (12 * k + 1) ∧
      Nat.Prime (18 * k + 1)) :
    {n : ℕ | IsThreePrimeCarmichael n}.Infinite := by
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨N, hN⟩
  obtain ⟨n, hn, hc⟩ := ThreePrimeCarmichaelInfinitude hDickson N
  exact absurd (hN hc) (by omega)

end Brockian.CarmichaelKorselt

