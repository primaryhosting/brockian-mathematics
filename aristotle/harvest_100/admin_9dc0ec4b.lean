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
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

open Finset

/-- Notation for the sum-of-divisors function `σ₁`. -/
local notation "σ₁" => ArithmeticFunction.sigma 1

/-! ## Definition -/

/-- A *betrothed* (or *quasi-amicable*) pair: two positive integers each of whose
sum of divisors equals the sum of the two numbers plus one. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ σ₁ m = m + n + 1 ∧ σ₁ n = m + n + 1

/-! ## The rational abundancy bound

The abundancy index `σ₁ n / n` is bounded above by `∏_{p ∣ n} p / (p - 1)`.  For an odd `n`
whose number of distinct prime factors is at most twenty, this product is at most
`∏_{p ≤ 73, p odd prime} p/(p-1) = 3.9668… < 4`. -/

/-- The twenty smallest odd primes. -/
def smallOddPrimes : Finset ℕ :=
  {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73}

/-- The map `p ↦ p / (p - 1)` is antitone on `[2, ∞)`. -/
lemma ratio_antitone {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (b : ℚ) / (b - 1) ≤ (a : ℚ) / (a - 1) := by
  have ha' : (2 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
  have hab' : (a : ℚ) ≤ (b : ℚ) := by exact_mod_cast hab
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Every odd prime below `79` is one of the twenty smallest odd primes. -/
lemma mem_smallOddPrimes {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h79 : p < 79) :
    p ∈ smallOddPrimes := by
  have h : ∀ q ∈ Finset.range 79, Nat.Prime q → q ≠ 2 → q ∈ smallOddPrimes := by decide
  exact h p (Finset.mem_range.mpr h79) hp h2

lemma card_smallOddPrimes : smallOddPrimes.card = 20 := by decide

lemma smallOddPrimes_bounds {p : ℕ} (hp : p ∈ smallOddPrimes) : 2 ≤ p ∧ p ≤ 79 := by
  revert hp; revert p; decide

/-- The product of `p / (p - 1)` over the twenty smallest odd primes is less than `4`. -/
lemma prod_smallOddPrimes_lt_four :
    ∏ p ∈ smallOddPrimes, ((p : ℚ) / (p - 1)) < 4 := by
  rw [show smallOddPrimes = ({3, 5, 7, 11, 13, 17, 19} : Finset ℕ) ∪
        (({23, 29, 31, 37, 41, 43, 47} : Finset ℕ) ∪ ({53, 59, 61, 67, 71, 73} : Finset ℕ))
      from by decide,
    Finset.prod_union (by decide), Finset.prod_union (by decide)]
  norm_num

/-- **Rational abundancy bound.** If `S` is a set of at most twenty odd primes, then
`∏_{p ∈ S} p / (p - 1) < 4`. -/
theorem prod_ratio_lt_four (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2)
    (hcard : S.card ≤ 20) :
    ∏ p ∈ S, ((p : ℚ) / (p - 1)) < 4 := by
  classical
  have hf2 : ∀ p : ℕ, 2 ≤ p → (0 : ℚ) < (p : ℚ) / (p - 1) := by
    intro p hp
    have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
    apply div_pos <;> linarith
  have h79 : ((79 : ℕ) : ℚ) / ((79 : ℕ) - 1) = 79 / 78 := by norm_num
  set A := S ∩ smallOddPrimes with hAdef
  set B := S \ smallOddPrimes with hBdef
  have hAS : A ⊆ S := Finset.inter_subset_left
  have hBS : B ⊆ S := Finset.sdiff_subset
  have hAP : A ⊆ smallOddPrimes := Finset.inter_subset_right
  have hsplit : (∏ p ∈ A, ((p : ℚ) / (p - 1))) * (∏ p ∈ B, ((p : ℚ) / (p - 1)))
      = ∏ p ∈ S, ((p : ℚ) / (p - 1)) := Finset.prod_inter_mul_prod_diff S smallOddPrimes _
  have hcards : A.card + B.card = S.card := Finset.card_inter_add_card_sdiff S smallOddPrimes
  set a : ℚ := ∏ p ∈ A, ((p : ℚ) / (p - 1)) with ha
  set b : ℚ := ∏ p ∈ B, ((p : ℚ) / (p - 1)) with hb
  set P : ℚ := ∏ p ∈ smallOddPrimes, ((p : ℚ) / (p - 1)) with hP
  have hApos : 0 < a := Finset.prod_pos (fun p hp => hf2 p (hS p (hAS hp)).1.two_le)
  have hBpos : 0 < b := Finset.prod_pos (fun p hp => hf2 p (hS p (hBS hp)).1.two_le)
  have hPpos : 0 < P := Finset.prod_pos (fun p hp => hf2 p (smallOddPrimes_bounds hp).1)
  -- primes outside `smallOddPrimes` are at least `79`, so contribute at most `79/78` each
  have hBbound : b ≤ (79 / 78 : ℚ) ^ B.card := by
    calc b ≤ ∏ _p ∈ B, (79 / 78 : ℚ) := by
          refine Finset.prod_le_prod (fun p hp => le_of_lt (hf2 p (hS p (hBS hp)).1.two_le)) ?_
          intro p hp
          have hp79 : 79 ≤ p := by
            by_contra hlt
            exact (Finset.mem_sdiff.mp hp).2
              (mem_smallOddPrimes (hS p (hBS hp)).1 (hS p (hBS hp)).2 (by omega))
          have hle := ratio_antitone (a := 79) (b := p) (by norm_num) hp79
          rwa [h79] at hle
      _ = (79 / 78 : ℚ) ^ B.card := by rw [Finset.prod_const]
  -- the small primes contribute at least `79/78` each
  have hg1 : ∀ p ∈ smallOddPrimes, (1 : ℚ) ≤ ((p : ℚ) / (p - 1)) * (78 / 79) := by
    intro p hp
    obtain ⟨h2, h73⟩ := smallOddPrimes_bounds hp
    have hle := ratio_antitone (a := p) (b := 79) h2 h73
    rw [h79] at hle
    linarith
  have hprodg : ∀ T : Finset ℕ, (∏ p ∈ T, (((p : ℚ) / (p - 1)) * (78 / 79)))
      = (∏ p ∈ T, ((p : ℚ) / (p - 1))) * (78 / 79 : ℚ) ^ T.card := by
    intro T; rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hone_le : (1 : ℚ) ≤ ∏ p ∈ smallOddPrimes \ A, (((p : ℚ) / (p - 1)) * (78 / 79)) := by
    calc (1 : ℚ) = ∏ _p ∈ smallOddPrimes \ A, (1 : ℚ) := by simp
      _ ≤ _ := Finset.prod_le_prod (by intros; norm_num)
          (fun p hp => hg1 p (Finset.mem_sdiff.mp hp).1)
  have hAg : (∏ p ∈ A, (((p : ℚ) / (p - 1)) * (78 / 79)))
      ≤ ∏ p ∈ smallOddPrimes, (((p : ℚ) / (p - 1)) * (78 / 79)) := by
    rw [← Finset.prod_sdiff hAP]
    have hpos : 0 < ∏ p ∈ A, (((p : ℚ) / (p - 1)) * (78 / 79)) := by
      rw [hprodg]; positivity
    nlinarith
  rw [hprodg, hprodg, card_smallOddPrimes, ← ha, ← hP] at hAg
  -- put the two estimates together
  have hc1 : (1 : ℚ) ≤ 79 / 78 := by norm_num
  have step1 : a * b ≤ a * (79 / 78 : ℚ) ^ B.card := by nlinarith
  have step2 : a * (79 / 78 : ℚ) ^ B.card
      = (a * (78 / 79 : ℚ) ^ A.card) * (79 / 78 : ℚ) ^ (A.card + B.card) := by
    have h1 : (78 / 79 : ℚ) ^ A.card * (79 / 78 : ℚ) ^ A.card = 1 := by
      rw [← mul_pow]; norm_num
    rw [pow_add]
    calc a * (79 / 78 : ℚ) ^ B.card
        = a * ((78 / 79 : ℚ) ^ A.card * (79 / 78 : ℚ) ^ A.card) * (79 / 78 : ℚ) ^ B.card := by
          rw [h1]; ring
      _ = a * (78 / 79 : ℚ) ^ A.card * ((79 / 78 : ℚ) ^ A.card * (79 / 78 : ℚ) ^ B.card) := by
          ring
  have step3 : (a * (78 / 79 : ℚ) ^ A.card) * (79 / 78 : ℚ) ^ (A.card + B.card)
      ≤ (P * (78 / 79 : ℚ) ^ 20) * (79 / 78 : ℚ) ^ (A.card + B.card) :=
    mul_le_mul_of_nonneg_right hAg (by positivity)
  have step4 : (P * (78 / 79 : ℚ) ^ 20) * (79 / 78 : ℚ) ^ (A.card + B.card)
      ≤ (P * (78 / 79 : ℚ) ^ 20) * (79 / 78 : ℚ) ^ 20 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hc1 (by omega)) (by positivity)
  have step5 : (P * (78 / 79 : ℚ) ^ 20) * (79 / 78 : ℚ) ^ 20 = P := by
    rw [mul_assoc, ← mul_pow]; norm_num
  rw [← hsplit]
  calc a * b ≤ P := by linarith
    _ < 4 := prod_smallOddPrimes_lt_four

/-! ## Elementary estimates for `σ₁` -/

/-- `σ₁ (p ^ a) * (p - 1) ≤ p ^ (a + 1)` for a prime `p`. -/
lemma sigma_primePow_mul_pred_le (p a : ℕ) (hp : p.Prime) :
    σ₁ (p ^ a) * (p - 1) ≤ p ^ (a + 1) := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_prime_pow hp]
  have h2 := hp.two_le
  induction a with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      calc (∑ x ∈ Finset.range (k + 1), p ^ x + p ^ (k + 1)) * (p - 1)
          = (∑ x ∈ Finset.range (k + 1), p ^ x) * (p - 1) + p ^ (k + 1) * (p - 1) := by ring
        _ ≤ p ^ (k + 1) + p ^ (k + 1) * (p - 1) := Nat.add_le_add_right ih _
        _ = p ^ (k + 1) * (1 + (p - 1)) := by ring
        _ = p ^ (k + 1) * p := by congr 1; omega
        _ = p ^ (k + 1 + 1) := by ring

/-- The integral form of the abundancy bound:
`σ₁ n * ∏_{p ∣ n} (p - 1) ≤ n * ∏_{p ∣ n} p`. -/
lemma sigma_mul_prod_pred_le {n : ℕ} (hn : n ≠ 0) :
    σ₁ n * ∏ p ∈ n.primeFactors, (p - 1) ≤ n * ∏ p ∈ n.primeFactors, p := by
  have h1 : σ₁ n = ∏ p ∈ n.primeFactors, σ₁ (p ^ n.factorization p) := by
    rw [ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hn]; rfl
  have h2 : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
    conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    rfl
  calc σ₁ n * ∏ p ∈ n.primeFactors, (p - 1)
      = ∏ p ∈ n.primeFactors, (σ₁ (p ^ n.factorization p) * (p - 1)) := by
        rw [h1, Finset.prod_mul_distrib]
    _ ≤ ∏ p ∈ n.primeFactors, (p ^ n.factorization p * p) := by
        refine Finset.prod_le_prod' ?_
        intro p hp
        calc σ₁ (p ^ n.factorization p) * (p - 1) ≤ p ^ (n.factorization p + 1) :=
              sigma_primePow_mul_pred_le p _ (Nat.prime_of_mem_primeFactors hp)
          _ = p ^ n.factorization p * p := by ring
    _ = n * ∏ p ∈ n.primeFactors, p := by rw [Finset.prod_mul_distrib, h2]

/-- An odd number whose abundancy index exceeds `4` has at least twenty-one distinct
prime factors. -/
theorem card_primeFactors_of_odd_of_four_mul_lt_sigma {N : ℕ} (hN : 0 < N) (hodd : Odd N)
    (habund : 4 * N < σ₁ N) : 21 ≤ N.primeFactors.card := by
  by_contra hcon
  push_neg at hcon
  have hcard : N.primeFactors.card ≤ 20 := by omega
  have hS : ∀ p ∈ N.primeFactors, p.Prime ∧ p ≠ 2 := by
    intro p hp
    refine ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩
    rintro rfl
    have h2 : (2 : ℕ) ∣ N := Nat.dvd_of_mem_primeFactors hp
    rw [Nat.odd_iff] at hodd
    omega
  -- the rational bound
  have hQ := prod_ratio_lt_four N.primeFactors hS hcard
  -- transfer to natural numbers
  set Q : ℕ := ∏ p ∈ N.primeFactors, p with hQdef
  set D : ℕ := ∏ p ∈ N.primeFactors, (p - 1) with hDdef
  have hDpos : 0 < D := by
    refine Finset.prod_pos ?_
    intro p hp
    have := (hS p hp).1.two_le
    omega
  have hcastD : (D : ℚ) = ∏ p ∈ N.primeFactors, ((p : ℚ) - 1) := by
    rw [hDdef, Nat.cast_prod]
    refine Finset.prod_congr rfl ?_
    intro p hp
    have := (hS p hp).1.two_le
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
    ring
  have hcastQ : (Q : ℚ) = ∏ p ∈ N.primeFactors, (p : ℚ) := by rw [hQdef, Nat.cast_prod]
  have hne : ∀ p ∈ N.primeFactors, ((p : ℚ) - 1) ≠ 0 := by
    intro p hp
    have := (hS p hp).1.two_le
    have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast this
    intro h; linarith
  have hprod_div : ∏ p ∈ N.primeFactors, ((p : ℚ) / (p - 1)) = (Q : ℚ) / (D : ℚ) := by
    rw [hcastQ, hcastD, ← Finset.prod_div_distrib]
  have hDQ : (Q : ℚ) < 4 * (D : ℚ) := by
    have hDpos' : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hDpos
    rw [hprod_div, div_lt_iff₀ hDpos'] at hQ
    linarith
  have hQD : Q < 4 * D := by exact_mod_cast hDQ
  -- contradiction
  have e1 : 4 * N * D < σ₁ N * D := by
    exact Nat.mul_lt_mul_of_lt_of_le habund (le_refl D) hDpos
  have e2 : σ₁ N * D ≤ N * Q := sigma_mul_prod_pred_le (by omega)
  have e3 : N * Q < N * (4 * D) := Nat.mul_lt_mul_of_pos_left hQD hN
  have e4 : N * (4 * D) = 4 * N * D := by ring
  omega

/-! ## Parity of `σ₁` and squares -/

/-- For an odd prime `p`, `σ₁ (p ^ a) ≡ a + 1 [MOD 2]`. -/
lemma sigma_primePow_mod_two {p : ℕ} (a : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    σ₁ (p ^ a) % 2 = (a + 1) % 2 := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_prime_pow hp]
  induction a with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, Nat.add_mod, ih]
      have hpk : p ^ (k + 1) % 2 = 1 := by rw [Nat.pow_mod, hodd]; simp
      omega

/-- A positive natural number is a square exactly when all exponents in its prime
factorization are even. -/
lemma isSquare_iff_even_factorization {n : ℕ} (hn : n ≠ 0) :
    IsSquare n ↔ ∀ p, Even (n.factorization p) := by
  constructor
  · rintro ⟨k, rfl⟩ p
    have hk : k ≠ 0 := by rintro rfl; simp at hn
    rw [Nat.factorization_mul hk hk]
    exact ⟨k.factorization p, rfl⟩
  · intro h
    refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
    rw [← Finset.prod_mul_distrib]
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    rw [Nat.prod_factorization_eq_prod_primeFactors]
    refine Finset.prod_congr rfl ?_
    intro p _
    rw [← pow_add]
    congr 1
    obtain ⟨t, ht⟩ := h p
    omega

/-- **Parity of the sum of divisors of an odd number.** For odd `n`, the sum of divisors
`σ₁ n` is odd if and only if `n` is a perfect square. -/
theorem odd_sigma_one_iff {n : ℕ} (hn : n ≠ 0) (hodd : Odd n) :
    Odd (σ₁ n) ↔ IsSquare n := by
  have hfac : σ₁ n = ∏ p ∈ n.primeFactors, σ₁ (p ^ n.factorization p) := by
    rw [ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hn]; rfl
  have hne2 : ∀ p ∈ n.primeFactors, p.Prime ∧ p ≠ 2 := by
    intro p hp
    refine ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩
    rintro rfl
    have h2 : (2 : ℕ) ∣ n := Nat.dvd_of_mem_primeFactors hp
    rw [Nat.odd_iff] at hodd
    omega
  rw [isSquare_iff_even_factorization hn]
  constructor
  · intro hs p
    by_cases hp : p ∈ n.primeFactors
    · by_contra hEven
      obtain ⟨hpp, hp2⟩ := hne2 p hp
      have h1 : σ₁ (p ^ n.factorization p) % 2 = 0 := by
        rw [sigma_primePow_mod_two _ hpp hp2]
        rcases Nat.even_or_odd (n.factorization p) with h | h
        · exact absurd h hEven
        · rw [Nat.odd_iff] at h; omega
      have h2 : σ₁ (p ^ n.factorization p) ∣ σ₁ n := by
        rw [hfac]; exact Finset.dvd_prod_of_mem _ hp
      have h3 : 2 ∣ σ₁ n := dvd_trans (Nat.dvd_of_mod_eq_zero h1) h2
      rw [Nat.odd_iff] at hs
      omega
    · have h0 : n.factorization p = 0 := by
        rw [← Nat.support_factorization] at hp
        exact Finsupp.notMem_support_iff.mp hp
      simp [h0]
  · intro h
    by_contra hno
    rw [Nat.not_odd_iff_even, even_iff_two_dvd, hfac,
      Prime.dvd_finset_prod_iff Nat.prime_two.prime] at hno
    obtain ⟨p, hp, hdvd⟩ := hno
    obtain ⟨hpp, hp2⟩ := hne2 p hp
    have hm := sigma_primePow_mod_two (n.factorization p) hpp hp2
    obtain ⟨t, ht⟩ := h p
    omega

/-! ## Hagis–Lord Proposition 2 (second part) -/

/-- A coprime betrothed pair whose members have the same parity consists of two odd numbers:
two even numbers cannot be coprime. -/
lemma odd_of_coprime_sameParity {m n : ℕ} (hcop : Nat.Coprime m n) (hpar : Even m ↔ Even n) :
    Odd m ∧ Odd n := by
  have hm : ¬ Even m := by
    intro hm
    have hn : Even n := hpar.mp hm
    have h2m : 2 ∣ m := hm.two_dvd
    have h2n : 2 ∣ n := hn.two_dvd
    have : (2 : ℕ) ∣ Nat.gcd m n := Nat.dvd_gcd h2m h2n
    rw [hcop] at this
    omega
  have hn : ¬ Even n := fun hn => hm (hpar.mpr hn)
  exact ⟨Nat.odd_iff.mpr (Nat.not_even_iff.mp hm), Nat.odd_iff.mpr (Nat.not_even_iff.mp hn)⟩

/-- The product of a coprime betrothed pair has abundancy index exceeding `4`:
`σ₁ (m * n) = (m + n + 1) ^ 2 > (m + n) ^ 2 ≥ 4 m n`. -/
lemma four_mul_lt_sigma_mul {m n : ℕ} (h : IsBetrothedPair m n) (hcop : Nat.Coprime m n) :
    4 * (m * n) < σ₁ (m * n) := by
  obtain ⟨-, -, hm, hn⟩ := h
  have hmul : σ₁ (m * n) = σ₁ m * σ₁ n :=
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
  rw [hmul, hm, hn]
  nlinarith [two_mul_le_add_sq m n, sq_nonneg (m + n)]

/-- **Hagis–Lord, Proposition 2 (second part).**
If `(m, n)` is a betrothed (quasi-amicable) pair which is coprime and whose two members have
the same parity, then both members are odd and the product `m * n` has at least twenty-one
distinct prime factors.

This is an exact, unconditional theorem.  It should not be confused with the *computational*
lower bounds attached to the same problem in the literature (for instance the statements that
a same-parity betrothed pair, if any exists, must exceed certain explicit numerical bounds):
those come from finite machine searches and are not formalized here. -/
theorem coprime_sameParity_twentyOne_primeFactors {m n : ℕ} (h : IsBetrothedPair m n)
    (hcop : Nat.Coprime m n) (hpar : Even m ↔ Even n) :
    Odd m ∧ Odd n ∧ 21 ≤ (m * n).primeFactors.card := by
  obtain ⟨hmodd, hnodd⟩ := odd_of_coprime_sameParity hcop hpar
  refine ⟨hmodd, hnodd, ?_⟩
  refine card_primeFactors_of_odd_of_four_mul_lt_sigma
    (Nat.mul_pos h.1 h.2.1) (hmodd.mul hnodd) (four_mul_lt_sigma_mul h hcop)

/-- **Hagis–Lord, Proposition 2 (first part).** Both members of a coprime same-parity
betrothed pair are perfect squares: they are odd, and their common value of `σ₁`, namely
`m + n + 1`, is odd, so `odd_sigma_one_iff` applies. -/
theorem coprime_sameParity_isSquare {m n : ℕ} (h : IsBetrothedPair m n)
    (hcop : Nat.Coprime m n) (hpar : Even m ↔ Even n) :
    IsSquare m ∧ IsSquare n := by
  obtain ⟨hmodd, hnodd⟩ := odd_of_coprime_sameParity hcop hpar
  obtain ⟨hm0, hn0, hsm, hsn⟩ := h
  have hsum : Odd (m + n + 1) := by
    rw [Nat.odd_iff] at hmodd hnodd ⊢
    omega
  refine ⟨?_, ?_⟩
  · exact (odd_sigma_one_iff (by omega) hmodd).mp (by rw [hsm]; exact hsum)
  · exact (odd_sigma_one_iff (by omega) hnodd).mp (by rw [hsn]; exact hsum)

/-! ## Sanity check and the status of the computational bounds

The smallest betrothed pair is `(48, 75)`; it has opposite parity (and is not coprime), so
it is not covered by the theorem above.  All known betrothed pairs have opposite parity, and
the *computational* results in the literature (searches showing that a same-parity pair, if
one exists, must exceed explicit numerical bounds) are finite machine verifications; they are
deliberately **not** formalized nor assumed anywhere in this file.  Everything above is an
unconditional theorem of Lean's core logic plus Mathlib. -/

example : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;> decide

end BetrothedNumbers
end Brockian

