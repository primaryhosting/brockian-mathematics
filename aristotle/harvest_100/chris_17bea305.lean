/-
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

/-!
## Betrothed (quasi-amicable) numbers

A pair `(m, n)` of positive integers is *betrothed* (or *quasi-amicable*) when each of the two
numbers is the sum of the **non-trivial** divisors of the other, i.e.

`σ(m) = σ(n) = m + n + 1`.

This file formalizes the second half of Proposition 2 of Hagis and Lord, *Quasi-amicable numbers*
(Math. Comp. 31 (1977)): if the two members of a betrothed pair are **coprime** and have the
**same parity**, then both are odd (indeed both are perfect squares) and the product `m * n` has
at least twenty-one distinct prime factors.

The proof is completely elementary:

* both members are odd, since two coprime numbers cannot both be even;
* therefore `σ(m) = m + n + 1` is odd, so `m` (and likewise `n`) is a perfect square, by
  `Brockian.BetrothedNumbers.odd_sigma_one_iff`;
* by coprimality `σ(mn) = σ(m)σ(n) = (m + n + 1)^2 > 4mn`, so the odd number `N = mn` has
  abundancy `σ(N)/N > 4`;
* the abundancy of `N` is bounded above by `∏_{p ∣ N} p/(p-1)`, and the product of `p/(p-1)`
  over any twenty distinct odd primes is at most the value taken over the twenty smallest odd
  primes `3, 5, …, 73`, which is `< 4`.

Hence `ω(mn) ≥ 21`. This bound is exactly what is proved here; it is a *theorem*, and should be
distinguished from the (much larger) **computational** lower bounds that appear in the
literature, which rest on extensive machine search rather than on proof. Such historical
numerical records — e.g. that no coprime betrothed pair of the same parity is known at all, and
that searches have ruled out all such pairs below various large bounds — are deliberately **not**
stated as Lean theorems anywhere in this file; only the unconditional inequality `21 ≤ ω(mn)` is.
-/

namespace Brockian.BetrothedNumbers

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- A *betrothed* (quasi-amicable) pair: `σ m = σ n = m + n + 1`, i.e. each number is the sum of
the non-trivial divisors (excluding `1` and the number itself) of the other. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  σ 1 m = m + n + 1 ∧ σ 1 n = m + n + 1

/-- The smallest betrothed pair, `(48, 75)`; it is neither coprime nor of the same parity,
consistently with the theorem below. -/
example : IsBetrothedPair 48 75 := by constructor <;> decide

/-- The factor `p / (p - 1)`: a strict upper bound for the abundancy `σ(p^a)/p^a`. -/
noncomputable def primeMult (p : ℕ) : ℚ := (p : ℚ) / ((p : ℚ) - 1)

/-- The twenty smallest odd primes. -/
def oddPrimes20 : Finset ℕ :=
  {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73}

/-! ### Parity of `σ` -/

/-- For odd `p`, the geometric sum `1 + p + ⋯ + p^(m-1)` has the same parity as `m`. -/
lemma sum_pow_mod_two {p : ℕ} (hp : Odd p) (m : ℕ) :
    (∑ i ∈ Finset.range m, p ^ i) % 2 = m % 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.odd_iff.mp hp.pow]
      omega

/-- An odd number has odd sum of divisors exactly when it is a perfect square. -/
lemma odd_sigma_one_iff {n : ℕ} (hn : Odd n) : Odd (σ 1 n) ↔ IsSquare n := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hn
  have hsig : σ 1 n = ∏ p ∈ n.primeFactors, ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i := by
    simpa using ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
      (k := 1) hn0
  have hodd : ∀ p ∈ n.primeFactors, Odd p := by
    intro p hp
    rcases (Nat.prime_of_mem_primeFactors hp).eq_two_or_odd' with rfl | h
    · obtain ⟨c, hc⟩ := Nat.dvd_of_mem_primeFactors hp; omega
    · exact h
  constructor
  · intro hsig_odd
    rw [Nat.odd_iff, hsig] at hsig_odd
    have hall : ∀ p ∈ n.primeFactors, Even (n.factorization p) := by
      intro p hp
      by_contra hodd'
      have h1 : (∑ i ∈ Finset.range (n.factorization p + 1), p ^ i) % 2 = 0 := by
        rw [sum_pow_mod_two (hodd p hp)]
        rcases Nat.even_or_odd (n.factorization p) with h | h
        · exact absurd h hodd'
        · rw [Nat.odd_iff] at h; omega
      have h2 : (2:ℕ) ∣ ∏ p ∈ n.primeFactors, ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i :=
        Dvd.dvd.trans (Nat.dvd_of_mod_eq_zero h1)
          (Finset.dvd_prod_of_mem (fun p => ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i) hp)
      omega
    refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
    rw [← Finset.prod_mul_distrib]
    conv_lhs => rw [show n = ∏ p ∈ n.primeFactors, p ^ n.factorization p by
      rw [← Nat.support_factorization, ← Finsupp.prod, Nat.factorization_prod_pow_eq_self hn0]]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    rw [← pow_add]
    congr 1
    obtain ⟨k, hk⟩ := hall p hp
    omega
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by rintro rfl; simp at hr; omega
    have hall : ∀ p, Even (n.factorization p) := by
      intro p
      rw [hr, Nat.factorization_mul hr0 hr0]
      simp only [Finsupp.add_apply]
      exact ⟨_, rfl⟩
    rw [Nat.odd_iff, hsig, Finset.prod_nat_mod]
    have h : ∀ p ∈ n.primeFactors, (∑ i ∈ Finset.range (n.factorization p + 1), p ^ i) % 2 = 1 := by
      intro p hp
      rw [sum_pow_mod_two (hodd p hp)]
      obtain ⟨k, hk⟩ := hall p
      omega
    rw [Finset.prod_congr rfl h]
    simp

/-! ### The abundancy bound `σ(N)/N ≤ ∏_{p ∣ N} p/(p-1)` -/

lemma sigma_prime_pow_div_le_primeMult {p a : ℕ} (hp : p.Prime) :
    ((∑ i ∈ Finset.range (a + 1), p ^ i : ℕ) : ℚ) / ((p : ℚ) ^ a) ≤ primeMult p := by
  have h2 : (2:ℚ) ≤ (p:ℚ) := by exact_mod_cast hp.two_le
  have hx1 : (0:ℚ) < (p:ℚ) - 1 := by linarith
  have hxa : (0:ℚ) < (p:ℚ) ^ a := by positivity
  rw [primeMult, div_le_div_iff₀ hxa hx1]
  push_cast
  calc (∑ i ∈ Finset.range (a + 1), (p:ℚ) ^ i) * ((p:ℚ) - 1) = (p:ℚ) ^ (a + 1) - 1 :=
        geom_sum_mul _ _
    _ ≤ (p:ℚ) * (p:ℚ) ^ a := by
        ring_nf; linarith [pow_pos (lt_of_lt_of_le two_pos h2) a]

/-- The abundancy of `N` is at most `∏_{p ∣ N} p/(p-1)`. -/
lemma sigma_div_le_prod_primeMult {N : ℕ} (hN : N ≠ 0) :
    (σ 1 N : ℚ) / (N : ℚ) ≤ ∏ p ∈ N.primeFactors, primeMult p := by
  have hsig : σ 1 N = ∏ p ∈ N.primeFactors, ∑ i ∈ Finset.range (N.factorization p + 1), p ^ i := by
    simpa using ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
      (k := 1) hN
  have hNprod : N = ∏ p ∈ N.primeFactors, p ^ N.factorization p := by
    rw [← Nat.support_factorization, ← Finsupp.prod, Nat.factorization_prod_pow_eq_self hN]
  rw [hsig, show ((N:ℚ)) = ∏ p ∈ N.primeFactors, ((p:ℚ) ^ N.factorization p) by
    conv_lhs => rw [hNprod]
    push_cast
    ring]
  push_cast
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_le_prod (fun p _ => by positivity) (fun p hp => ?_)
  have h := sigma_prime_pow_div_le_primeMult (p := p) (a := N.factorization p)
    (Nat.prime_of_mem_primeFactors hp)
  push_cast at h
  exact h

/-! ### The extremal product over twenty odd primes -/

lemma one_le_primeMult {p : ℕ} (hp : 2 ≤ p) : 1 ≤ primeMult p := by
  have h2 : (2:ℚ) ≤ (p:ℚ) := by exact_mod_cast hp
  rw [primeMult, le_div_iff₀ (by linarith)]
  linarith

lemma primeMult_pos {p : ℕ} (hp : 2 ≤ p) : 0 < primeMult p :=
  lt_of_lt_of_le one_pos (one_le_primeMult hp)

lemma primeMult_anti {p q : ℕ} (hq : 2 ≤ q) (hqp : q ≤ p) : primeMult p ≤ primeMult q := by
  have h2 : (2:ℚ) ≤ (q:ℚ) := by exact_mod_cast hq
  have h3 : (q:ℚ) ≤ (p:ℚ) := by exact_mod_cast hqp
  rw [primeMult, primeMult, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

lemma one_le_prod_primeMult {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) :
    1 ≤ ∏ p ∈ S, primeMult p := by
  calc (1:ℚ) = ∏ _i ∈ S, (1:ℚ) := by simp
    _ ≤ ∏ i ∈ S, primeMult i := Finset.prod_le_prod (fun i _ => zero_le_one)
        (fun i hi => one_le_primeMult (hS i hi))

lemma mem_oddPrimes20 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hle : p ≤ 73) : p ∈ oddPrimes20 := by
  have h : ∀ q < 74, q.Prime → q ≠ 2 → q ∈ oddPrimes20 := by decide
  exact h p (by omega) hp h2

lemma oddPrimes20_spec {p : ℕ} (hp : p ∈ oddPrimes20) : p.Prime ∧ p ≠ 2 ∧ p ≤ 73 := by
  revert hp
  have h : ∀ q ∈ oddPrimes20, q.Prime ∧ q ≠ 2 ∧ q ≤ 73 := by decide
  exact h p

/-- Exchange argument: replacing an odd prime outside the twenty smallest odd primes by an
unused one among them only increases the product of the factors `p/(p-1)`. -/
lemma prod_primeMult_le_aux (k : ℕ) : ∀ S : Finset ℕ, (S \ oddPrimes20).card = k →
    (∀ p ∈ S, p.Prime ∧ p ≠ 2) → S.card ≤ 20 →
    ∏ p ∈ S, primeMult p ≤ ∏ p ∈ oddPrimes20, primeMult p := by
  induction k with
  | zero =>
      intro S hk hS _
      have hsub : S ⊆ oddPrimes20 := by
        rwa [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hk
      rw [← Finset.prod_sdiff hsub]
      have h1 : (1:ℚ) ≤ ∏ p ∈ oddPrimes20 \ S, primeMult p :=
        one_le_prod_primeMult (fun i hi => (oddPrimes20_spec (Finset.mem_sdiff.mp hi).1).1.two_le)
      have h2 : (0:ℚ) < ∏ p ∈ S, primeMult p :=
        Finset.prod_pos (fun i hi => primeMult_pos (hS i hi).1.two_le)
      nlinarith
  | succ k ih =>
      intro S hk hS hcard
      have hne : (S \ oddPrimes20).Nonempty := by
        rw [← Finset.card_pos, hk]; omega
      obtain ⟨p, hpmem⟩ := hne
      have hpS : p ∈ S := (Finset.mem_sdiff.mp hpmem).1
      have hpP : p ∉ oddPrimes20 := (Finset.mem_sdiff.mp hpmem).2
      have hp73 : 73 < p := by
        by_contra hcon
        exact hpP (mem_oddPrimes20 (hS p hpS).1 (hS p hpS).2 (by omega))
      have hc1 : (S \ oddPrimes20).card + (S ∩ oddPrimes20).card = S.card :=
        Finset.card_sdiff_add_card_inter S oddPrimes20
      have hc2 : (oddPrimes20 \ S).card + (oddPrimes20 ∩ S).card = oddPrimes20.card :=
        Finset.card_sdiff_add_card_inter oddPrimes20 S
      have hc3 : (oddPrimes20 ∩ S).card = (S ∩ oddPrimes20).card := by rw [Finset.inter_comm]
      have hc4 : oddPrimes20.card = 20 := by decide
      have hqne : (oddPrimes20 \ S).Nonempty := by rw [← Finset.card_pos]; omega
      obtain ⟨q, hqmem⟩ := hqne
      have hqP : q ∈ oddPrimes20 := (Finset.mem_sdiff.mp hqmem).1
      have hqS : q ∉ S := (Finset.mem_sdiff.mp hqmem).2
      obtain ⟨hqprime, hq2, hq73⟩ := oddPrimes20_spec hqP
      set T := S.erase p with hT
      have hqT : q ∉ T := fun h => hqS (Finset.mem_of_mem_erase h)
      have hS' : ∀ x ∈ insert q T, x.Prime ∧ x ≠ 2 := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact ⟨hqprime, hq2⟩
        · exact hS x (Finset.mem_of_mem_erase hx)
      have hcardT : T.card + 1 = S.card := by
        rw [hT, Finset.card_erase_of_mem hpS]
        have : 1 ≤ S.card := Finset.card_pos.mpr ⟨p, hpS⟩
        omega
      have hcard' : (insert q T).card ≤ 20 := by
        rw [Finset.card_insert_of_notMem hqT]; omega
      have hsd : ((insert q T) \ oddPrimes20).card = k := by
        rw [Finset.insert_sdiff_of_mem _ hqP]
        have hTP : T \ oddPrimes20 = (S \ oddPrimes20).erase p := by
          rw [hT, Finset.erase_sdiff_comm]
        rw [hTP, Finset.card_erase_of_mem hpmem, hk]
        omega
      have hIH := ih (insert q T) hsd hS' hcard'
      have hprodT : (0:ℚ) < ∏ x ∈ T, primeMult x :=
        Finset.prod_pos (fun i hi => primeMult_pos (hS i (Finset.mem_of_mem_erase hi)).1.two_le)
      have h1 : ∏ x ∈ S, primeMult x = primeMult p * ∏ x ∈ T, primeMult x := by
        rw [hT, Finset.mul_prod_erase _ _ hpS]
      have h2 : ∏ x ∈ insert q T, primeMult x = primeMult q * ∏ x ∈ T, primeMult x :=
        Finset.prod_insert hqT
      have hle : primeMult p ≤ primeMult q := primeMult_anti hqprime.two_le (by omega)
      rw [h1]
      rw [h2] at hIH
      nlinarith

/-- Over any at most twenty distinct odd primes, `∏ p/(p-1)` is maximal for the twenty
smallest odd primes. -/
lemma prod_primeMult_le_of_odd_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2)
    (hcard : S.card ≤ 20) :
    ∏ p ∈ S, primeMult p ≤ ∏ p ∈ oddPrimes20, primeMult p :=
  prod_primeMult_le_aux (S \ oddPrimes20).card S rfl hS hcard

lemma prod_oddPrimes20_lt_four : ∏ p ∈ oddPrimes20, primeMult p < 4 := by
  simp [oddPrimes20, primeMult, Finset.prod_insert, Finset.mem_insert]
  norm_num

/-! ### The main theorem -/

/-- **Hagis–Lord, Proposition 2 (second part).**  If `(m, n)` is a betrothed (quasi-amicable)
pair whose members are coprime and of the same parity, then both members are odd perfect
squares and `m * n` has at least twenty-one distinct prime factors.

This is the exact, unconditional statement; it is independent of the far larger *computational*
lower bounds recorded in the literature, which are not formalized here. -/
theorem coprime_sameParity_twentyOne_primeFactors {m n : ℕ}
    (h : IsBetrothedPair m n) (hcop : Nat.Coprime m n) (hpar : m % 2 = n % 2) :
    Odd m ∧ Odd n ∧ IsSquare m ∧ IsSquare n ∧ 21 ≤ (m * n).primeFactors.card := by
  obtain ⟨hm, hn⟩ := h
  -- both members are nonzero
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp only [ArithmeticFunction.map_zero] at hm
    omega
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [ArithmeticFunction.map_zero] at hn
    omega
  -- both members are odd
  have hmodd : Odd m := by
    rw [Nat.odd_iff]
    by_contra hcon
    have h2m : 2 ∣ m := by omega
    have h2n : 2 ∣ n := by omega
    have : (2:ℕ) ∣ Nat.gcd m n := Nat.dvd_gcd h2m h2n
    rw [Nat.Coprime] at hcop
    omega
  have hnodd : Odd n := by rw [Nat.odd_iff]; rw [Nat.odd_iff] at hmodd; omega
  -- hence both are perfect squares
  have hsum_odd : Odd (m + n + 1) := by
    rw [Nat.odd_iff]
    rw [Nat.odd_iff] at hmodd hnodd
    omega
  have hmsq : IsSquare m := (odd_sigma_one_iff hmodd).mp (hm ▸ hsum_odd)
  have hnsq : IsSquare n := (odd_sigma_one_iff hnodd).mp (hn ▸ hsum_odd)
  refine ⟨hmodd, hnodd, hmsq, hnsq, ?_⟩
  by_contra hcon
  push_neg at hcon
  have hcard : (m * n).primeFactors.card ≤ 20 := by omega
  have hN0 : m * n ≠ 0 := Nat.mul_ne_zero hm0 hn0
  -- σ(mn) = (m+n+1)^2
  have hsig : σ 1 (m * n) = (m + n + 1) * (m + n + 1) := by
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hm, hn]
  -- every prime factor of mn is odd
  have hodd_pf : ∀ p ∈ (m * n).primeFactors, p.Prime ∧ p ≠ 2 := by
    intro p hp
    refine ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩
    rintro rfl
    have h2 : (2:ℕ) ∣ m * n := Nat.dvd_of_mem_primeFactors hp
    have : Odd (m * n) := hmodd.mul hnodd
    rw [Nat.odd_iff] at this
    omega
  -- the abundancy bound
  have hbound := sigma_div_le_prod_primeMult hN0
  have hb2 := prod_primeMult_le_of_odd_primes hodd_pf hcard
  have hb3 : (σ 1 (m * n) : ℚ) / ((m * n : ℕ) : ℚ) < 4 :=
    lt_of_le_of_lt (le_trans hbound hb2) prod_oddPrimes20_lt_four
  have hpos : (0:ℚ) < ((m * n : ℕ) : ℚ) := by
    have : 0 < m * n := Nat.pos_of_ne_zero hN0
    exact_mod_cast this
  rw [div_lt_iff₀ hpos, hsig] at hb3
  push_cast at hb3
  have hm1 : (1:ℚ) ≤ (m:ℚ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0
  have hn1 : (1:ℚ) ≤ (n:ℚ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  nlinarith [sq_nonneg ((m:ℚ) - (n:ℚ))]

end Brockian.BetrothedNumbers

