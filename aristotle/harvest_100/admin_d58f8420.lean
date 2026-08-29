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

/-- A *Carmichael number*: a composite `n > 1` such that `a ^ (n - 1) ≡ 1 [MOD n]` for every
`a` coprime to `n` (i.e. a Fermat pseudoprime to every admissible base). -/
def IsCarmichael (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ a : ℕ, Nat.Coprime a n → a ^ (n - 1) ≡ 1 [MOD n]

/-- A squarefree number is divisible by any number that all of its prime factors divide. -/
theorem dvd_of_squarefree_of_forall_prime_dvd {n m : ℕ} (hsq : Squarefree n)
    (h : ∀ p ∈ n.primeFactors, p ∣ m) : n ∣ m := by
  have hn0 : n ≠ 0 := hsq.ne_zero
  rcases eq_or_ne m 0 with rfl | hm
  · exact dvd_zero n
  rw [← Nat.factorization_le_iff_dvd hn0 hm]
  intro p
  rcases Nat.eq_zero_or_pos (n.factorization p) with hp | hp
  · simp [hp]
  · have hmem : p ∈ n.primeFactors := by
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.mpr hp.ne'
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hmem
    calc n.factorization p ≤ 1 := Squarefree.natFactorization_le_one p hsq
      _ ≤ m.factorization p := hprime.factorization_pos_of_dvd hm (h p hmem)

/-- **Korselt's criterion** (sufficiency): a squarefree composite `n > 1` all of whose prime
factors `p` satisfy `(p - 1) ∣ (n - 1)` is a Carmichael number. -/
theorem isCarmichael_of_korselt {n : ℕ} (h1 : 1 < n) (hnp : ¬ n.Prime) (hsq : Squarefree n)
    (hk : ∀ p ∈ n.primeFactors, (p - 1) ∣ (n - 1)) : IsCarmichael n := by
  refine ⟨h1, hnp, fun a ha => ?_⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at ha
    omega
  have hpow : 1 ≤ a ^ (n - 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero ha0)
  have hdvd : n ∣ a ^ (n - 1) - 1 := by
    refine dvd_of_squarefree_of_forall_prime_dvd hsq ?_
    · intro p hp
      have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      have hap : Nat.Coprime a p := Nat.Coprime.coprime_dvd_right hpn ha
      obtain ⟨t, ht⟩ := hk p hp
      have hfermat : a ^ (p - 1) ≡ 1 [MOD p] := by
        have := Nat.ModEq.pow_totient hap
        rwa [Nat.totient_prime hprime] at this
      have : a ^ (n - 1) ≡ 1 [MOD p] := by
        calc a ^ (n - 1) = (a ^ (p - 1)) ^ t := by rw [← pow_mul, ← ht]
          _ ≡ 1 ^ t [MOD p] := hfermat.pow t
          _ = 1 := one_pow t
      exact (Nat.modEq_iff_dvd' hpow).mp this.symm
  exact ((Nat.modEq_iff_dvd' hpow).mpr hdvd).symm

/-- The three prime factors in Chernick's construction are pairwise distinct (for `k ≥ 1`). -/
theorem chernick_lt {k : ℕ} (hk : 0 < k) : 6 * k + 1 < 12 * k + 1 ∧ 12 * k + 1 < 18 * k + 1 := by
  omega

/-- **Chernick's construction.** If `6k+1`, `12k+1`, `18k+1` are all prime (with `k ≥ 1`), then
their product is a Carmichael number with exactly three prime factors. -/
theorem chernick_isCarmichael {k : ℕ} (hk : 0 < k) (h6 : (6 * k + 1).Prime)
    (h12 : (12 * k + 1).Prime) (h18 : (18 * k + 1).Prime) :
    IsCarmichael ((6 * k + 1) * (12 * k + 1) * (18 * k + 1)) ∧
      ((6 * k + 1) * (12 * k + 1) * (18 * k + 1)).primeFactors.card = 3 := by
  set p := 6 * k + 1 with hp
  set q := 12 * k + 1 with hq
  set r := 18 * k + 1 with hr
  set n := p * q * r with hn
  have hpq : p ≠ q := by omega
  have hpr : p ≠ r := by omega
  have hqr : q ≠ r := by omega
  have hcpq : Nat.Coprime p q := (Nat.coprime_primes h6 h12).mpr hpq
  have hcpr : Nat.Coprime p r := (Nat.coprime_primes h6 h18).mpr hpr
  have hcqr : Nat.Coprime q r := (Nat.coprime_primes h12 h18).mpr hqr
  have hfac : n.primeFactors = {p, q, r} := by
    rw [hn, Nat.primeFactors_mul (by positivity) h18.ne_zero,
      Nat.primeFactors_mul h6.ne_zero h12.ne_zero, h6.primeFactors, h12.primeFactors,
      h18.primeFactors]
    ext x
    simp [or_assoc]
  have hcard : n.primeFactors.card = 3 := by
    rw [hfac]
    rw [Finset.card_insert_of_notMem
        (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hpq, hpr⟩),
      Finset.card_insert_of_notMem (by simpa using hqr), Finset.card_singleton]
  have hsq : Squarefree n := by
    have h1 : Squarefree (p * q) := by
      rw [Nat.squarefree_mul hcpq]
      exact ⟨h6.squarefree, h12.squarefree⟩
    rw [hn, Nat.squarefree_mul (Nat.Coprime.mul_left hcpr hcqr)]
    exact ⟨h1, h18.squarefree⟩
  have hn1 : 1 < n := by
    have : 1 * 1 * 1 < n := by
      rw [hn]
      exact Nat.mul_lt_mul_of_lt_of_lt (Nat.mul_lt_mul_of_lt_of_lt (by omega) (by omega))
        (by omega)
    simpa using this
  have hnp : ¬ n.Prime := by
    intro hprime
    have : n.primeFactors.card = 1 := by rw [hprime.primeFactors]; simp
    omega
  have hnval : n - 1 = 36 * k * (36 * k * k + 11 * k + 1) := by
    have : n = 1296 * (k * k * k) + 396 * (k * k) + 36 * k + 1 := by
      rw [hn, hp, hq, hr]; ring
    rw [this]; ring_nf; omega
  refine ⟨isCarmichael_of_korselt hn1 hnp hsq ?_, hcard⟩
  intro s hs
  rw [hfac] at hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  have h36 : (36 * k) ∣ (n - 1) := ⟨36 * k * k + 11 * k + 1, hnval⟩
  rcases hs with rfl | rfl | rfl
  · exact dvd_trans ⟨6, by omega⟩ h36
  · exact dvd_trans ⟨3, by omega⟩ h36
  · exact dvd_trans ⟨2, by omega⟩ h36

/-- **Conditional infinitude of three-prime Carmichael numbers.**

Whether there are infinitely many Carmichael numbers with exactly three prime factors is an
open problem.  The theorem below is a Lean-checked conditional reduction: assuming the
Dickson-type hypothesis that `6k+1`, `12k+1`, `18k+1` are simultaneously prime for infinitely
many `k` (a special case of Dickson's conjecture), the set of Carmichael numbers with exactly
three prime factors is infinite. -/
theorem ThreePrimeCarmichaelInfinitude
    (hD : {k : ℕ | (6 * k + 1).Prime ∧ (12 * k + 1).Prime ∧ (18 * k + 1).Prime}.Infinite) :
    {n : ℕ | IsCarmichael n ∧ n.primeFactors.card = 3}.Infinite := by
  set S := {k : ℕ | (6 * k + 1).Prime ∧ (12 * k + 1).Prime ∧ (18 * k + 1).Prime} with hS
  set T := S \ {0} with hT
  have hTinf : T.Infinite := hD.diff (Set.finite_singleton 0)
  set f : ℕ → ℕ := fun k => (6 * k + 1) * (12 * k + 1) * (18 * k + 1) with hf
  have hmono : StrictMono f := by
    intro a b hab
    simp only [hf]
    exact Nat.mul_lt_mul_of_lt_of_lt
      (Nat.mul_lt_mul_of_lt_of_lt (by omega) (by omega)) (by omega)
  have hinj : Set.InjOn f T := hmono.injective.injOn
  have hsub : f '' T ⊆ {n : ℕ | IsCarmichael n ∧ n.primeFactors.card = 3} := by
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨⟨h6, h12, h18⟩, hk0⟩ := hk
    exact chernick_isCarmichael (Nat.pos_of_ne_zero (by simpa using hk0)) h6 h12 h18
  exact (Set.Infinite.image hinj hTinf).mono hsub

end Brockian.CarmichaelKorselt

