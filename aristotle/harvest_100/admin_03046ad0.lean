/-
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

open Finset

/-! ## Basic definitions -/

/-- `sigmaOne n` is the sum-of-divisors function `σ₁(n) = ∑_{d ∣ n} d`. -/
def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- A *betrothed pair* (quasi-amicable pair): two distinct positive integers each of whose
divisor sums equals `m + n + 1`, i.e. the sum of the proper divisors of each (excluding `1`
and the number itself) equals the other. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigmaOne m = m + n + 1 ∧ sigmaOne n = m + n + 1

/-- The local abundancy weight `w p = p / (p - 1)`, an upper bound for the abundancy
contributed by the prime `p`. -/
noncomputable def w (p : ℕ) : ℚ := (p : ℚ) / ((p : ℚ) - 1)

/-! ## The rational abundancy bound `σ₁(N)/N ≤ ∏_{p ∣ N} p/(p-1)` -/

lemma one_le_w {p : ℕ} (hp : 2 ≤ p) : 1 ≤ w p := by
  have h2 : (2:ℚ) ≤ (p:ℚ) := by exact_mod_cast hp
  unfold w
  rw [le_div_iff₀ (by linarith)]
  linarith

lemma w_nonneg {p : ℕ} (hp : 2 ≤ p) : 0 ≤ w p :=
  le_trans zero_le_one (one_le_w hp)

lemma w_anti {a c : ℕ} (ha : 2 ≤ a) (hac : a ≤ c) : w c ≤ w a := by
  have h2 : (2:ℚ) ≤ (a:ℚ) := by exact_mod_cast ha
  have h3 : (a:ℚ) ≤ (c:ℚ) := by exact_mod_cast hac
  unfold w
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

lemma sigmaOne_prime_pow_le {p k : ℕ} (hp : p.Prime) :
    (sigmaOne (p ^ k) : ℚ) ≤ (p : ℚ) ^ k * w p := by
  have hp2 : (2:ℚ) ≤ (p:ℚ) := by exact_mod_cast hp.two_le
  have hd : (0:ℚ) < (p:ℚ) - 1 := by linarith
  have hs : (sigmaOne (p ^ k) : ℚ) = ∑ i ∈ Finset.range (k + 1), (p:ℚ) ^ i := by
    unfold sigmaOne
    rw [Nat.sum_divisors_prime_pow hp]
    push_cast
    ring_nf
  rw [hs, geom_sum_eq (by linarith)]
  have hw : (p:ℚ) ^ k * w p = ((p:ℚ) ^ (k + 1)) / ((p:ℚ) - 1) := by
    unfold w; field_simp; ring
  rw [hw]
  gcongr
  linarith

/-- The rational abundancy bound: `σ₁(N) ≤ N ∏_{p ∣ N} p/(p-1)`. -/
lemma sigmaOne_le_mul_prod_w :
    ∀ (N : ℕ), N ≠ 0 → (sigmaOne N : ℚ) ≤ (N : ℚ) * ∏ p ∈ N.primeFactors, w p := by
  intro N
  induction N using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
      intro _
      rw [Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton]
      push_cast
      exact sigmaOne_prime_pow_le hp
  | zero => intro h; exact absurd rfl h
  | one => intro _; simp [sigmaOne]
  | coprime a b ha hb hab iha ihb =>
      intro _
      have ha0 : a ≠ 0 := by omega
      have hb0 : b ≠ 0 := by omega
      have hsig : (sigmaOne (a * b) : ℚ) = (sigmaOne a : ℚ) * (sigmaOne b : ℚ) := by
        unfold sigmaOne
        rw [hab.sum_divisors_mul]
        push_cast
        ring
      have hpf : (a * b).primeFactors = a.primeFactors ∪ b.primeFactors := hab.primeFactors_mul
      have hdisj : Disjoint a.primeFactors b.primeFactors := hab.disjoint_primeFactors
      rw [hsig, hpf, Finset.prod_union hdisj]
      have h1 := iha ha0
      have h2 := ihb hb0
      have hA : 0 ≤ ∏ p ∈ a.primeFactors, w p :=
        Finset.prod_nonneg fun p hp => w_nonneg (Nat.prime_of_mem_primeFactors hp).two_le
      have hB : 0 ≤ ∏ p ∈ b.primeFactors, w p :=
        Finset.prod_nonneg fun p hp => w_nonneg (Nat.prime_of_mem_primeFactors hp).two_le
      calc (sigmaOne a : ℚ) * (sigmaOne b : ℚ)
          ≤ ((a:ℚ) * ∏ p ∈ a.primeFactors, w p) * ((b:ℚ) * ∏ p ∈ b.primeFactors, w p) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = ((a * b : ℕ) : ℚ) * ((∏ p ∈ a.primeFactors, w p) * ∏ p ∈ b.primeFactors, w p) := by
            push_cast; ring

/-! ## The greedy bound on `∏ p/(p-1)` over a set of odd primes -/

/-- The twenty smallest odd primes. -/
def oddPrimes20 : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73]

lemma one_le_prod_map_w :
    ∀ (L : List ℕ), (∀ b ∈ L, 2 ≤ b) → 1 ≤ (L.map w).prod := by
  intro L
  induction L with
  | nil => simp
  | cons b T ih =>
      intro h
      simp only [List.map_cons, List.prod_cons]
      have h1 := one_le_w (h b (by simp))
      have h2 := ih fun x hx => h x (by simp [hx])
      nlinarith

/-- Greedy comparison: if every element of `S` is a prime bounded below by the head of a
"gap chain" list `L`, and `S` has at most `L.length` elements, then `∏_{p ∈ S} w p` is at most
the product of `w` over `L`. -/
lemma prod_w_le_of_gapChain :
    ∀ (L : List ℕ) (S : Finset ℕ),
      (∀ b ∈ L, 2 ≤ b) →
      L.IsChain (fun a b => ∀ p : ℕ, p.Prime → a < p → b ≤ p) →
      (∀ p ∈ S, p.Prime) →
      (∀ b ∈ L.head?, ∀ p ∈ S, b ≤ p) →
      S.card ≤ L.length →
      ∏ p ∈ S, w p ≤ (L.map w).prod := by
  intro L
  induction L with
  | nil =>
      intro S _ _ _ _ hcard
      simp only [List.length_nil, Nat.le_zero, Finset.card_eq_zero] at hcard
      simp [hcard]
  | cons b T ih =>
      intro S hb2 hchain hprime hhead hcard
      rcases Finset.eq_empty_or_nonempty S with rfl | hS
      · simpa using one_le_prod_map_w (b :: T) hb2
      · set m := S.min' hS with hm
        have hmS : m ∈ S := S.min'_mem hS
        have hbm : b ≤ m := hhead b (by simp) m hmS
        have hb2' : 2 ≤ b := hb2 b (by simp)
        rw [List.isChain_cons] at hchain
        obtain ⟨hrel, hchainT⟩ := hchain
        have hsplit : ∏ p ∈ S, w p = w m * ∏ p ∈ S.erase m, w p :=
          (Finset.mul_prod_erase S w hmS).symm
        have hIH : ∏ p ∈ S.erase m, w p ≤ (T.map w).prod := by
          refine ih (S.erase m) (fun x hx => hb2 x (by simp [hx])) hchainT
            (fun p hp => hprime p (Finset.mem_of_mem_erase hp)) ?_ ?_
          · intro b' hb' p hp
            have hpS : p ∈ S := Finset.mem_of_mem_erase hp
            have hne : p ≠ m := Finset.ne_of_mem_erase hp
            have hmp : m ≤ p := S.min'_le p hpS
            exact hrel b' hb' p (hprime p hpS) (by omega)
          · have hce := Finset.card_erase_of_mem hmS
            simp only [List.length_cons] at hcard
            omega
        have hwm : w m ≤ w b := w_anti hb2' hbm
        have hnn : 0 ≤ ∏ p ∈ S.erase m, w p :=
          Finset.prod_nonneg fun p hp =>
            w_nonneg (hprime p (Finset.mem_of_mem_erase hp)).two_le
        simp only [List.map_cons, List.prod_cons]
        rw [hsplit]
        exact mul_le_mul hwm hIH hnn (w_nonneg hb2')

lemma oddPrimes20_gapChain :
    oddPrimes20.IsChain (fun a b => ∀ p : ℕ, p.Prime → a < p → b ≤ p) := by
  simp only [oddPrimes20, List.isChain_cons_cons, List.isChain_singleton, and_true]
  and_intros <;>
    (intro p hp h; by_contra hc; push_neg at hc; interval_cases p <;> revert hp <;> decide)

lemma prod_map_w_oddPrimes20_lt_four : (oddPrimes20.map w).prod < 4 := by
  simp only [oddPrimes20, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, w]
  norm_num

/-- If `N` is odd and its abundancy exceeds `4`, then `N` has at least `21` distinct prime
factors. -/
lemma twentyOne_le_card_primeFactors_of_odd_of_four_mul_lt
    {N : ℕ} (hN : N ≠ 0) (hodd : Odd N) (h4 : 4 * N < sigmaOne N) :
    21 ≤ N.primeFactors.card := by
  by_contra hcon
  push_neg at hcon
  have hcard : N.primeFactors.card ≤ oddPrimes20.length := by
    simp only [oddPrimes20, List.length_cons, List.length_nil]
    omega
  have hprime : ∀ p ∈ N.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hthree : ∀ p ∈ N.primeFactors, 3 ≤ p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hdvd : p ∣ N := Nat.dvd_of_mem_primeFactors hp
    have hne : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
    have := hpp.two_le
    omega
  have hbound : ∏ p ∈ N.primeFactors, w p ≤ (oddPrimes20.map w).prod := by
    refine prod_w_le_of_gapChain oddPrimes20 N.primeFactors (by intro b hb; fin_cases hb <;> norm_num)
      oddPrimes20_gapChain hprime ?_ hcard
    intro b hb p hp
    simp only [oddPrimes20, List.head?_cons, Option.mem_def, Option.some.injEq] at hb
    subst hb
    exact hthree p hp
  have hNpos : (0:ℚ) < (N:ℚ) := by
    have : 0 < N := Nat.pos_of_ne_zero hN
    exact_mod_cast this
  have hle := sigmaOne_le_mul_prod_w N hN
  have hlt : (sigmaOne N : ℚ) < 4 * (N:ℚ) := by
    calc (sigmaOne N : ℚ) ≤ (N : ℚ) * ∏ p ∈ N.primeFactors, w p := hle
      _ ≤ (N : ℚ) * (oddPrimes20.map w).prod := by
          exact mul_le_mul_of_nonneg_left hbound (le_of_lt hNpos)
      _ < (N : ℚ) * 4 := by
          exact mul_lt_mul_of_pos_left prod_map_w_oddPrimes20_lt_four hNpos
      _ = 4 * (N:ℚ) := by ring
  have h4' : (4 * N : ℚ) < (sigmaOne N : ℚ) := by exact_mod_cast h4
  push_cast at h4'
  linarith

/-! ## Parity of the divisor sum: `odd_sigma_one_iff` -/

/-- A nonzero natural number is a perfect square iff every exponent in its prime
factorization is even. -/
lemma isSquare_iff_factorization_even {n : ℕ} (hn : n ≠ 0) :
    IsSquare n ↔ ∀ p, Even (n.factorization p) := by
  constructor
  · rintro ⟨r, rfl⟩ p
    have hr : r ≠ 0 := by rintro rfl; simp at hn
    rw [Nat.factorization_mul hr hr]
    simp
  · intro h
    refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
    rw [← Finset.prod_mul_distrib]
    have key : ∀ p ∈ n.primeFactors,
        p ^ (n.factorization p / 2) * p ^ (n.factorization p / 2) = p ^ (n.factorization p) := by
      intro p _
      rw [← pow_add]
      congr 1
      obtain ⟨j, hj⟩ := h p
      omega
    rw [Finset.prod_congr rfl key]
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    rw [Nat.prod_factorization_eq_prod_primeFactors]

lemma geom_sum_mod_two {p : ℕ} (hp : Odd p) :
    ∀ k, (∑ i ∈ Finset.range k, p ^ i) % 2 = k % 2 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.odd_iff.mp hp.pow]
      omega

lemma isSquare_prime_pow_iff {p k : ℕ} (hp : p.Prime) : IsSquare (p ^ k) ↔ Even k := by
  constructor
  · intro h
    rw [isSquare_iff_factorization_even (pow_ne_zero k hp.pos.ne')] at h
    have hpk := h p
    rwa [Nat.factorization_pow_self hp] at hpk
  · rintro ⟨j, rfl⟩
    exact ⟨p ^ j, by rw [← pow_add]⟩

lemma coprime_isSquare_mul_iff {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) :
    IsSquare (a * b) ↔ IsSquare a ∧ IsSquare b := by
  rw [isSquare_iff_factorization_even (Nat.mul_ne_zero ha hb),
    isSquare_iff_factorization_even ha, isSquare_iff_factorization_even hb,
    Nat.factorization_mul ha hb]
  constructor
  · intro h
    have hdisj : Disjoint a.primeFactors b.primeFactors := hab.disjoint_primeFactors
    constructor <;> intro p <;> have hp := h p <;> simp only [Finsupp.add_apply] at hp
    · by_cases h0 : a.factorization p = 0
      · simp [h0]
      · have hmem : p ∈ a.primeFactors := by
          rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.mpr h0
        have hnot : p ∉ b.primeFactors := Finset.disjoint_left.mp hdisj hmem
        have h1 : b.factorization p = 0 := by
          rw [← Nat.support_factorization] at hnot
          exact Finsupp.notMem_support_iff.mp hnot
        rwa [h1, add_zero] at hp
    · by_cases h0 : b.factorization p = 0
      · simp [h0]
      · have hmem : p ∈ b.primeFactors := by
          rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.mpr h0
        have hnot : p ∉ a.primeFactors := Finset.disjoint_right.mp hdisj hmem
        have h1 : a.factorization p = 0 := by
          rw [← Nat.support_factorization] at hnot
          exact Finsupp.notMem_support_iff.mp hnot
        rwa [h1, zero_add] at hp
  · rintro ⟨h1, h2⟩ p
    simpa using (h1 p).add (h2 p)

/-- For a positive odd `n`, the divisor sum `σ₁(n)` is odd exactly when `n` is a perfect
square. -/
theorem odd_sigma_one_iff :
    ∀ n : ℕ, n ≠ 0 → Odd n → (Odd (sigmaOne n) ↔ IsSquare n) := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
      intro _ hoddpk
      have hpodd : Odd p := by
        rcases hp.eq_two_or_odd' with rfl | h
        · exact absurd hoddpk (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, hk.ne'⟩))
        · exact h
      have hs : sigmaOne (p ^ k) = ∑ i ∈ Finset.range (k + 1), p ^ i := by
        unfold sigmaOne; rw [Nat.sum_divisors_prime_pow hp]
      rw [hs, isSquare_prime_pow_iff hp, Nat.odd_iff, geom_sum_mod_two hpodd, Nat.even_iff]
      omega
  | zero => intro h; exact absurd rfl h
  | one => intro _ _; simp [sigmaOne]
  | coprime a b ha hb hab iha ihb =>
      intro _ hodd
      have ha0 : a ≠ 0 := by omega
      have hb0 : b ≠ 0 := by omega
      have hoa : Odd a := (Nat.odd_mul.mp hodd).1
      have hob : Odd b := (Nat.odd_mul.mp hodd).2
      have hsig : sigmaOne (a * b) = sigmaOne a * sigmaOne b := by
        unfold sigmaOne; rw [hab.sum_divisors_mul]
      rw [hsig, Nat.odd_mul, coprime_isSquare_mul_iff ha0 hb0 hab, iha ha0 hoa, ihb hb0 hob]

/-! ## Main theorem -/

/-- **Second part of Hagis–Lord, Proposition 2.**
If `(m, n)` is a betrothed (quasi-amicable) pair whose members are coprime and of the same
parity, then both members are odd and the product `m * n` has at least twenty-one distinct
prime factors.

This is the exact, unconditional statement.  It should not be confused with the purely
*computational* lower bounds in the literature (for instance, that no betrothed pair below
some search limit has coprime same-parity members); those are numerical search results and
are not formalized here. -/
theorem coprime_sameParity_twentyOne_primeFactors {m n : ℕ}
    (hpair : IsBetrothedPair m n) (hcop : Nat.Coprime m n) (hpar : m % 2 = n % 2) :
    Odd m ∧ Odd n ∧ 21 ≤ (m * n).primeFactors.card := by
  obtain ⟨hm0, hn0, hmn, hsm, hsn⟩ := hpair
  -- Both members are odd: two even members would share the factor `2`.
  have hmodd : m % 2 = 1 := by
    rcases Nat.even_or_odd m with he | ho
    · exfalso
      have hm2 : m % 2 = 0 := Nat.even_iff.mp he
      have h2m : 2 ∣ m := Nat.dvd_of_mod_eq_zero hm2
      have h2n : 2 ∣ n := Nat.dvd_of_mod_eq_zero (by omega)
      have hg : (2:ℕ) ∣ Nat.gcd m n := Nat.dvd_gcd h2m h2n
      rw [hcop] at hg
      exact absurd (Nat.le_of_dvd one_pos hg) (by norm_num)
    · exact Nat.odd_iff.mp ho
  have hnodd : n % 2 = 1 := by omega
  refine ⟨Nat.odd_iff.mpr hmodd, Nat.odd_iff.mpr hnodd, ?_⟩
  -- The product is odd and its abundancy exceeds 4.
  have hprododd : Odd (m * n) := (Nat.odd_iff.mpr hmodd).mul (Nat.odd_iff.mpr hnodd)
  have hne : m * n ≠ 0 := by positivity
  have hsig : sigmaOne (m * n) = (m + n + 1) * (m + n + 1) := by
    unfold sigmaOne
    rw [hcop.sum_divisors_mul]
    unfold sigmaOne at hsm hsn
    rw [hsm, hsn]
  have hgt : 4 * (m * n) < sigmaOne (m * n) := by
    rw [hsig]
    zify
    nlinarith [sq_nonneg ((m : ℤ) - (n : ℤ)), (by exact_mod_cast hm0 : (0:ℤ) < m),
      (by exact_mod_cast hn0 : (0:ℤ) < n)]
  exact twentyOne_le_card_primeFactors_of_odd_of_four_mul_lt hne hprododd hgt

/-- Companion to the main theorem (first half of the same Hagis–Lord proposition): the two
members of a coprime same-parity betrothed pair are perfect squares.  This is where
`odd_sigma_one_iff` is used. -/
theorem coprime_sameParity_isSquare {m n : ℕ}
    (hpair : IsBetrothedPair m n) (hcop : Nat.Coprime m n) (hpar : m % 2 = n % 2) :
    IsSquare m ∧ IsSquare n := by
  obtain ⟨hom, hon, -⟩ := coprime_sameParity_twentyOne_primeFactors hpair hcop hpar
  obtain ⟨hm0, hn0, -, hsm, hsn⟩ := hpair
  have hm2 : m % 2 = 1 := Nat.odd_iff.mp hom
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hon
  have hsumodd : Odd (m + n + 1) := Nat.odd_iff.mpr (by omega)
  refine ⟨(odd_sigma_one_iff m hm0.ne' hom).mp (by rw [hsm]; exact hsumodd),
    (odd_sigma_one_iff n hn0.ne' hon).mp (by rw [hsn]; exact hsumodd)⟩

/-!
## Remark: exact theorem versus historical computational bounds

The theorems above (`coprime_sameParity_twentyOne_primeFactors` and
`coprime_sameParity_isSquare`) are *exact, unconditional* statements about every coprime
same-parity betrothed pair.

They are deliberately kept separate from the *computational* results in the literature on
betrothed numbers — for example, numerical searches showing that no betrothed pair up to a
given search bound has coprime same-parity members, or numerical lower bounds on the size of
such a hypothetical pair.  Those depend on finite computer searches over ranges that are not
reproduced here, and none of them is asserted or used in this file.
-/

end BetrothedNumbers
end Brockian

