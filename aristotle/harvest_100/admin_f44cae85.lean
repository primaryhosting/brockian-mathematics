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

-- (The header above uses `/-` rather than `/-!` because Lean 4 does not permit a module
-- docstring to precede the `import` block; the text is otherwise verbatim.)

import Mathlib

/-!
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CarmichaelKorselt

/-- `n` is a Carmichael number: it is composite, yet `a ^ n ≡ a [ZMOD n]` for every integer `a`. -/
def IsCarmichael (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ a : ℤ, (n : ℤ) ∣ a ^ n - a

/-- The (open) hypothesis that Chernick's construction produces infinitely many prime
triples: for every `N` there is `k > N` with `6k+1`, `12k+1`, `18k+1` all prime.
This is a special case of Dickson's conjecture. -/
def ChernickPrimeTriples : Prop :=
  ∀ N : ℕ, ∃ k > N, Nat.Prime (6 * k + 1) ∧ Nat.Prime (12 * k + 1) ∧ Nat.Prime (18 * k + 1)

/-- The Korselt step for a single prime: if `p` is prime, `n ≥ 1` and `(p-1) ∣ (n-1)`,
then `p ∣ a ^ n - a` for every integer `a`. -/
theorem prime_dvd_pow_sub_self {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hd : (p - 1) ∣ (n - 1)) (a : ℤ) : (p : ℤ) ∣ a ^ n - a := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht⟩ := hd
  have hn' : n = (p - 1) * t + 1 := by omega
  have key : ((a : ZMod p)) ^ n = (a : ZMod p) := by
    by_cases h0 : (a : ZMod p) = 0
    · rw [h0, zero_pow (by omega)]
    · rw [hn', pow_add, pow_one, pow_mul, ZMod.pow_card_sub_one_eq_one h0, one_pow, one_mul]
  have hzero : ((a ^ n - a : ℤ) : ZMod p) = 0 := by push_cast; rw [key]; ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hzero

/-- Korselt's criterion (sufficiency) for a product of three distinct primes. -/
theorem isCarmichael_of_korselt_three {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hdp : (p - 1) ∣ (p * q * r - 1)) (hdq : (q - 1) ∣ (p * q * r - 1))
    (hdr : (r - 1) ∣ (p * q * r - 1)) : IsCarmichael (p * q * r) := by
  set n := p * q * r with hn
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hr2 := hr.two_le
  have hn1 : 1 < n := by
    have h8 : 2 * 2 * 2 ≤ n := Nat.mul_le_mul (Nat.mul_le_mul hp2 hq2) hr2
    omega
  refine ⟨hn1, ?_, ?_⟩
  · intro hprime
    have hdvd : p ∣ n := ⟨q * r, by rw [hn]; ring⟩
    rcases Nat.Prime.eq_one_or_self_of_dvd hprime p hdvd with h | h
    · omega
    · have hqr1 : q * r = 1 := by
        have hp0 : 0 < p := by omega
        have hcalc : p * (q * r) = p * 1 :=
          calc p * (q * r) = p * q * r := by ring
            _ = n := hn.symm
            _ = p := h.symm
            _ = p * 1 := (mul_one p).symm
        exact Nat.eq_of_mul_eq_mul_left hp0 hcalc
      have hq1 : q ≤ 1 := Nat.le_of_dvd Nat.one_pos ⟨r, hqr1.symm⟩
      omega
  · intro a
    have hdp' := prime_dvd_pow_sub_self hp (by omega) hdp a
    have hdq' := prime_dvd_pow_sub_self hq (by omega) hdq a
    have hdr' := prime_dvd_pow_sub_self hr (by omega) hdr a
    have cpq : IsCoprime (p : ℤ) (q : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hpq)
    have cpr : IsCoprime (p : ℤ) (r : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hr).mpr hpr)
    have cqr : IsCoprime (q : ℤ) (r : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hq hr).mpr hqr)
    have h1 : ((p : ℤ) * q) ∣ a ^ n - a := cpq.mul_dvd hdp' hdq'
    have h2 : ((p : ℤ) * q * r) ∣ a ^ n - a := (cpr.mul_left cqr).mul_dvd h1 hdr'
    have hcast : ((n : ℕ) : ℤ) = (p : ℤ) * q * r := by rw [hn]; push_cast; ring
    rw [hcast]
    exact h2

/-- Chernick numbers `(6k+1)(12k+1)(18k+1)` with all three factors prime are Carmichael
numbers with exactly three prime factors. -/
theorem chernick_isCarmichael {k : ℕ} (hk : 1 ≤ k)
    (hp : Nat.Prime (6 * k + 1)) (hq : Nat.Prime (12 * k + 1)) (hr : Nat.Prime (18 * k + 1)) :
    IsCarmichael ((6 * k + 1) * (12 * k + 1) * (18 * k + 1)) ∧
      Squarefree ((6 * k + 1) * (12 * k + 1) * (18 * k + 1)) ∧
      ((6 * k + 1) * (12 * k + 1) * (18 * k + 1)).primeFactors.card = 3 := by
  set p := 6 * k + 1 with hpdef
  set q := 12 * k + 1 with hqdef
  set r := 18 * k + 1 with hrdef
  have hpq : p ≠ q := by simp only [hpdef, hqdef]; omega
  have hpr : p ≠ r := by simp only [hpdef, hrdef]; omega
  have hqr : q ≠ r := by simp only [hqdef, hrdef]; omega
  have hprod : p * q * r = 36 * k * (36 * k ^ 2 + 11 * k + 1) + 1 := by
    simp only [hpdef, hqdef, hrdef]; ring
  have hsub : p * q * r - 1 = 36 * k * (36 * k ^ 2 + 11 * k + 1) := by omega
  have hdp : (p - 1) ∣ (p * q * r - 1) := by
    rw [hsub]
    have hp1 : p - 1 = 6 * k := by simp only [hpdef]; omega
    exact hp1 ▸ ⟨6 * (36 * k ^ 2 + 11 * k + 1), by ring⟩
  have hdq : (q - 1) ∣ (p * q * r - 1) := by
    rw [hsub]
    have hq1 : q - 1 = 12 * k := by simp only [hqdef]; omega
    exact hq1 ▸ ⟨3 * (36 * k ^ 2 + 11 * k + 1), by ring⟩
  have hdr : (r - 1) ∣ (p * q * r - 1) := by
    rw [hsub]
    have hr1 : r - 1 = 18 * k := by simp only [hrdef]; omega
    exact hr1 ▸ ⟨2 * (36 * k ^ 2 + 11 * k + 1), by ring⟩
  refine ⟨isCarmichael_of_korselt_three hp hq hr hpq hpr hqr hdp hdq hdr, ?_, ?_⟩
  · have cpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
    have cpr : Nat.Coprime p r := (Nat.coprime_primes hp hr).mpr hpr
    have cqr : Nat.Coprime q r := (Nat.coprime_primes hq hr).mpr hqr
    rw [Nat.squarefree_mul_iff]
    refine ⟨Nat.Coprime.mul_left cpr cqr, ?_, hr.squarefree⟩
    rw [Nat.squarefree_mul_iff]
    exact ⟨cpq, hp.squarefree, hq.squarefree⟩
  · have hp0 : p ≠ 0 := hp.ne_zero
    have hq0 : q ≠ 0 := hq.ne_zero
    have hr0 : r ≠ 0 := hr.ne_zero
    rw [Nat.primeFactors_mul (Nat.mul_ne_zero hp0 hq0) hr0, Nat.primeFactors_mul hp0 hq0,
      hp.primeFactors, hq.primeFactors, hr.primeFactors, Finset.union_assoc,
      Finset.card_union_of_disjoint (by simp [hpq, hpr]),
      Finset.card_union_of_disjoint (by simp [hqr])]
    simp

/-- Sanity check that the hypotheses above are satisfiable: `1729 = 7 * 13 * 19` is a
Carmichael number with exactly three prime factors. -/
theorem isCarmichael_1729 :
    IsCarmichael 1729 ∧ Squarefree 1729 ∧ (1729).primeFactors.card = 3 := by
  have h := chernick_isCarmichael (k := 1) le_rfl (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- **Conditional infinitude of three-prime Carmichael numbers.**

Assuming the (open) Chernick prime-triple hypothesis — a special case of Dickson's
conjecture — there are infinitely many Carmichael numbers that are squarefree and have
exactly three prime factors. -/
theorem ThreePrimeCarmichaelInfinitude (h : ChernickPrimeTriples) :
    ∀ N : ℕ, ∃ n > N, IsCarmichael n ∧ Squarefree n ∧ n.primeFactors.card = 3 := by
  intro N
  obtain ⟨k, hkN, hp, hq, hr⟩ := h N
  have hk : 1 ≤ k := by omega
  refine ⟨(6 * k + 1) * (12 * k + 1) * (18 * k + 1), ?_, chernick_isCarmichael hk hp hq hr⟩
  have h1 : 18 * k + 1 ≤ (6 * k + 1) * (12 * k + 1) * (18 * k + 1) :=
    Nat.le_mul_of_pos_left _ (by positivity)
  omega

end Brockian.CarmichaelKorselt

