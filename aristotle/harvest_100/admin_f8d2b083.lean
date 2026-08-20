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

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- `Betrothed m n` says that `(m, n)` is a betrothed (quasi-amicable) pair:
both are positive and `σ m = σ n = m + n + 1`. -/
def Betrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ σ 1 m = m + n + 1 ∧ σ 1 n = m + n + 1

/-! ## The rational abundancy bound -/

/-- The local Euler factor bound `p / (p - 1)` attached to a prime `p`. -/
noncomputable def primeRatio (p : ℕ) : ℚ := (p : ℚ) / ((p : ℚ) - 1)

lemma one_le_primeRatio {p : ℕ} (hp : 2 ≤ p) : 1 ≤ primeRatio p := by
  have h1 : (1 : ℚ) ≤ (p : ℚ) - 1 := by
    have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
    linarith
  rw [primeRatio, le_div_iff₀ (by linarith)]
  linarith

lemma primeRatio_nonneg {p : ℕ} (hp : 2 ≤ p) : 0 ≤ primeRatio p :=
  le_trans zero_le_one (one_le_primeRatio hp)

lemma primeRatio_le_of_le {p q : ℕ} (hq : 2 ≤ q) (hqp : q ≤ p) :
    primeRatio p ≤ primeRatio q := by
  have hq' : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hqp' : (q : ℚ) ≤ (p : ℚ) := by exact_mod_cast hqp
  rw [primeRatio, primeRatio, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- The local bound `σ (p ^ a) ≤ p ^ a * (p / (p - 1))`. -/
lemma sigma_primePow_le {p : ℕ} (hp : 2 ≤ p) (a : ℕ) :
    ((∑ k ∈ range (a + 1), p ^ k : ℕ) : ℚ) ≤ (p : ℚ) ^ a * primeRatio p := by
  have hp' : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
  have hp1 : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  have hcast : ((∑ k ∈ range (a + 1), p ^ k : ℕ) : ℚ) = ∑ k ∈ range (a + 1), (p : ℚ) ^ k := by
    push_cast; ring
  rw [hcast, geom_sum_eq (by linarith) (a + 1), primeRatio]
  rw [div_le_iff₀ hp1]
  have : (p : ℚ) ^ a * ((p : ℚ) / ((p : ℚ) - 1)) * ((p : ℚ) - 1) = (p : ℚ) ^ (a + 1) := by
    field_simp; ring
  rw [this]
  have : (p : ℚ) ^ (a + 1) - 1 ≤ (p : ℚ) ^ (a + 1) := by linarith
  linarith

/-- **Rational abundancy bound**: `σ n ≤ n * ∏_{p ∣ n} p / (p - 1)`. -/
lemma sigma_one_le_mul_prod_primeRatio {n : ℕ} (hn : n ≠ 0) :
    (σ 1 n : ℚ) ≤ (n : ℚ) * ∏ p ∈ n.primeFactors, primeRatio p := by
  have hnfac : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
    (Nat.factorization_prod_pow_eq_self hn).symm
  have hsig : σ 1 n = ∏ p ∈ n.primeFactors, ∑ k ∈ range (n.factorization p + 1), p ^ k := by
    rw [sigma_one_apply]; exact Nat.sum_divisors hn
  rw [hsig]
  have hcast : ((∏ p ∈ n.primeFactors, ∑ k ∈ range (n.factorization p + 1), p ^ k : ℕ) : ℚ)
      = ∏ p ∈ n.primeFactors, ((∑ k ∈ range (n.factorization p + 1), p ^ k : ℕ) : ℚ) := by
    push_cast; ring
  rw [hcast]
  have hRHS : (n : ℚ) * ∏ p ∈ n.primeFactors, primeRatio p
      = ∏ p ∈ n.primeFactors, ((p : ℚ) ^ n.factorization p * primeRatio p) := by
    rw [Finset.prod_mul_distrib]
    congr 1
    calc (n : ℚ) = ((∏ p ∈ n.primeFactors, p ^ n.factorization p : ℕ) : ℚ) := by
            exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) hnfac
      _ = ∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p := by push_cast; ring
  rw [hRHS]
  refine Finset.prod_le_prod (fun p _ => by positivity) (fun p hp => ?_)
  exact sigma_primePow_le (Nat.prime_of_mem_primeFactors hp).two_le _

/-! ## Parity of `σ`

The classical characterisation `σ n` odd ↔ `n` a square (for odd `n`), used to see that the
members of a coprime same-parity betrothed pair are perfect squares. -/

/-- For odd `p`, the geometric sum `1 + p + ⋯ + p ^ (m-1)` has the same parity as `m`. -/
lemma sum_pow_mod_two {p : ℕ} (hp : Odd p) (m : ℕ) : (∑ k ∈ range m, p ^ k) % 2 = m % 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have : p ^ m % 2 = 1 := Nat.odd_iff.mp hp.pow
      omega

/-- For a positive odd `n`, the divisor sum `σ n` is odd if and only if `n` is a perfect square. -/
lemma odd_sigma_one_iff {n : ℕ} (hn : n ≠ 0) (hodd : Odd n) : Odd (σ 1 n) ↔ IsSquare n := by
  have hfac : σ 1 n = ∏ p ∈ n.primeFactors, ∑ k ∈ range (n.factorization p + 1), p ^ k := by
    rw [sigma_one_apply]; exact Nat.sum_divisors hn
  have hpodd : ∀ p ∈ n.primeFactors, Odd p := by
    intro p hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
    exact Nat.Prime.odd_of_ne_two (Nat.prime_of_mem_primeFactors hp) hp2
  constructor
  · intro hos
    have heven : ∀ p ∈ n.primeFactors, Even (n.factorization p) := by
      intro p hp
      by_contra hcon
      have hodd' : Odd (n.factorization p) := Nat.not_even_iff_odd.mp hcon
      have h2 : 2 ∣ ∑ k ∈ range (n.factorization p + 1), p ^ k := by
        have := sum_pow_mod_two (hpodd p hp) (n.factorization p + 1)
        have h3 := Nat.odd_iff.mp hodd'
        omega
      have hdvd : 2 ∣ σ 1 n := hfac ▸ dvd_trans h2 (Finset.dvd_prod_of_mem _ hp)
      exact (Nat.not_even_iff_odd.mpr hos) (even_iff_two_dvd.mpr hdvd)
    have hnfac : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
      (Nat.factorization_prod_pow_eq_self hn).symm
    refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
    rw [← Finset.prod_mul_distrib]
    conv_lhs => rw [hnfac]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    rw [← pow_add]
    congr 1
    obtain ⟨t, ht⟩ := heven p hp
    omega
  · rintro ⟨r, rfl⟩
    have hr : r ≠ 0 := by rintro rfl; simp at hn
    rw [hfac, Nat.odd_iff, ← Nat.not_even_iff, even_iff_two_dvd]
    intro hdvd
    obtain ⟨p, hp, hpd⟩ := (Nat.Prime.prime Nat.prime_two).exists_mem_finset_dvd hdvd
    have hfp : (r * r).factorization p = 2 * r.factorization p := by
      rw [Nat.factorization_mul hr hr]; simp [two_mul]
    have hpar : ((r * r).factorization p + 1) % 2 = 1 := by rw [hfp]; omega
    have := sum_pow_mod_two (hpodd p hp) ((r * r).factorization p + 1)
    omega

/-! ## Only twenty odd primes are not enough -/

/-- The set of odd primes below `b`. -/
def oddPrimesBelow (b : ℕ) : Finset ℕ := (range b).filter (fun p => Nat.Prime p ∧ p ≠ 2)

/-- `bnd k` is the `(k+1)`-st odd prime, so that `oddPrimesBelow (bnd k)` consists of
the `k` smallest odd primes. -/
def bnd (k : ℕ) : ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79].getD k 0

lemma two_le_bnd {k : ℕ} (hk : k ≤ 20) : 2 ≤ bnd k := by
  interval_cases k <;> decide

lemma bnd_le_succ {k : ℕ} (hk : k < 20) : bnd k ≤ bnd (k + 1) := by
  interval_cases k <;> decide

lemma oddPrimesBelow_succ {k : ℕ} (hk : k < 20) :
    oddPrimesBelow (bnd (k + 1)) = insert (bnd k) (oddPrimesBelow (bnd k)) := by
  interval_cases k <;> decide

lemma oddPrimesBelow_mono {a b : ℕ} (hab : a ≤ b) : oddPrimesBelow a ⊆ oddPrimesBelow b := by
  intro p hp
  simp only [oddPrimesBelow, Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨lt_of_lt_of_le hp.1 hab, hp.2⟩

lemma one_le_primeRatio_of_mem {b p : ℕ} (hp : p ∈ oddPrimesBelow b) : 1 ≤ primeRatio p := by
  simp only [oddPrimesBelow, Finset.mem_filter, Finset.mem_range] at hp
  exact one_le_primeRatio hp.2.1.two_le

lemma one_le_prod_primeRatio {S : Finset ℕ} (h : ∀ p ∈ S, 1 ≤ primeRatio p) :
    1 ≤ ∏ p ∈ S, primeRatio p := by
  calc (1 : ℚ) = ∏ _p ∈ S, (1 : ℚ) := by simp
    _ ≤ ∏ p ∈ S, primeRatio p :=
        Finset.prod_le_prod (fun _ _ => zero_le_one) (fun p hp => h p hp)

lemma prod_primeRatio_le_of_subset {S T : Finset ℕ} (hst : S ⊆ T)
    (h1 : ∀ p ∈ T, 1 ≤ primeRatio p) :
    ∏ p ∈ S, primeRatio p ≤ ∏ p ∈ T, primeRatio p := by
  rw [← Finset.prod_sdiff hst]
  have hA : 1 ≤ ∏ p ∈ T \ S, primeRatio p :=
    one_le_prod_primeRatio (fun p hp => h1 p (Finset.mem_sdiff.mp hp).1)
  have hB : 0 ≤ ∏ p ∈ S, primeRatio p :=
    le_trans zero_le_one (one_le_prod_primeRatio (fun p hp => h1 p (hst hp)))
  nlinarith

/-- Greedy comparison: a set of at most `k` odd primes has `∏ p/(p-1)` at most the
corresponding product over the `k` smallest odd primes. -/
lemma prod_primeRatio_le_prod_oddPrimesBelow :
    ∀ k : ℕ, k ≤ 20 → ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p ∧ p ≠ 2) → S.card ≤ k →
      ∏ p ∈ S, primeRatio p ≤ ∏ q ∈ oddPrimesBelow (bnd k), primeRatio q := by
  intro k
  induction k with
  | zero =>
      intro _ S _ hc
      have : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hc)
      subst this
      simp only [Finset.prod_empty]
      exact one_le_prod_primeRatio (fun q hq => one_le_primeRatio_of_mem hq)
  | succ k ih =>
      intro hk S hS hc
      have hk' : k < 20 := by omega
      by_cases hbig : ∃ p ∈ S, bnd k ≤ p
      · obtain ⟨p, hpS, hple⟩ := hbig
        have hcard : (S.erase p).card ≤ k := by
          have := Finset.card_erase_of_mem hpS
          omega
        have hIH := ih (by omega) (S.erase p) (fun q hq => hS q (Finset.mem_of_mem_erase hq)) hcard
        have hprod : ∏ q ∈ S, primeRatio q = primeRatio p * ∏ q ∈ S.erase p, primeRatio q :=
          (Finset.mul_prod_erase _ _ hpS).symm
        have hnotmem : bnd k ∉ oddPrimesBelow (bnd k) := by
          simp only [oddPrimesBelow, Finset.mem_filter, Finset.mem_range]
          omega
        have hstep : ∏ q ∈ oddPrimesBelow (bnd (k + 1)), primeRatio q
            = primeRatio (bnd k) * ∏ q ∈ oddPrimesBelow (bnd k), primeRatio q := by
          rw [oddPrimesBelow_succ hk', Finset.prod_insert hnotmem]
        rw [hprod, hstep]
        have h1 : primeRatio p ≤ primeRatio (bnd k) :=
          primeRatio_le_of_le (two_le_bnd (by omega)) hple
        have h2 : (0 : ℚ) ≤ ∏ q ∈ S.erase p, primeRatio q :=
          Finset.prod_nonneg (fun q hq => primeRatio_nonneg (hS q (Finset.mem_of_mem_erase hq)).1.two_le)
        have h3 : (0 : ℚ) ≤ primeRatio (bnd k) := primeRatio_nonneg (two_le_bnd (by omega))
        exact mul_le_mul h1 hIH h2 h3
      · push_neg at hbig
        have hsub : S ⊆ oddPrimesBelow (bnd (k + 1)) := by
          intro p hp
          have hlt : p < bnd k := hbig p hp
          have := oddPrimesBelow_mono (bnd_le_succ hk')
          apply this
          simp only [oddPrimesBelow, Finset.mem_filter, Finset.mem_range]
          exact ⟨hlt, (hS p hp).1, (hS p hp).2⟩
        exact prod_primeRatio_le_of_subset hsub (fun q hq => one_le_primeRatio_of_mem hq)

/-- The twenty smallest odd primes. -/
def T20 : Finset ℕ :=
  ({3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73} : Finset ℕ)

lemma oddPrimesBelow_79 : oddPrimesBelow 79 = T20 := by decide

lemma three_le_of_mem_T20 : ∀ p ∈ T20, 3 ≤ p := by decide

lemma prod_T20_lt_four_prod_pred : (∏ p ∈ T20, p) < 4 * ∏ p ∈ T20, (p - 1) := by decide

lemma prod_oddPrimesBelow_79_lt_four : ∏ q ∈ oddPrimesBelow 79, primeRatio q < 4 := by
  rw [oddPrimesBelow_79]
  have hdiv : ∏ p ∈ T20, primeRatio p = (∏ p ∈ T20, (p : ℚ)) / ∏ p ∈ T20, ((p : ℚ) - 1) := by
    rw [← Finset.prod_div_distrib]; rfl
  have hpos : (0 : ℚ) < ∏ p ∈ T20, ((p : ℚ) - 1) := by
    apply Finset.prod_pos
    intro p hp
    have h3 : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast three_le_of_mem_T20 p hp
    linarith
  rw [hdiv, div_lt_iff₀ hpos]
  have hcast1 : (∏ p ∈ T20, (p : ℚ)) = ((∏ p ∈ T20, p : ℕ) : ℚ) := by push_cast; ring
  have hcast2 : (∏ p ∈ T20, ((p : ℚ) - 1)) = ((∏ p ∈ T20, (p - 1) : ℕ) : ℚ) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have h1 : 1 ≤ p := le_trans (by norm_num) (three_le_of_mem_T20 p hp)
    rw [Nat.cast_sub h1, Nat.cast_one]
  rw [hcast1, hcast2]
  have hnat : ((∏ p ∈ T20, p : ℕ) : ℚ) < ((4 * ∏ p ∈ T20, (p - 1) : ℕ) : ℚ) := by
    exact_mod_cast prod_T20_lt_four_prod_pred
  push_cast at hnat ⊢
  linarith

/-- Any set of at most twenty odd primes has `∏ p/(p-1) < 4`. -/
lemma prod_primeRatio_lt_four {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p ∧ p ≠ 2)
    (hc : S.card ≤ 20) : ∏ p ∈ S, primeRatio p < 4 := by
  have h := prod_primeRatio_le_prod_oddPrimesBelow 20 le_rfl S hS hc
  have hb : bnd 20 = 79 := by decide
  rw [hb] at h
  exact lt_of_le_of_lt h prod_oddPrimesBelow_79_lt_four

/-! ## The main theorem -/

/-- **Hagis–Lord, Proposition 2 (second part).**  If `(m, n)` is a coprime betrothed pair
whose members have the same parity, then both members are odd and the product `m * n`
has at least twenty-one distinct prime factors. -/
theorem coprime_sameParity_twentyOne_primeFactors {m n : ℕ} (h : Betrothed m n)
    (hcop : Nat.Coprime m n) (hpar : m % 2 = n % 2) :
    Odd m ∧ Odd n ∧ 21 ≤ (m * n).primeFactors.card := by
  obtain ⟨hm0, hn0, hsm, hsn⟩ := h
  -- both are odd
  have hmodd : m % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one m with h2 | h2
    · exfalso
      have hdm : 2 ∣ m := Nat.dvd_of_mod_eq_zero h2
      have hdn : 2 ∣ n := Nat.dvd_of_mod_eq_zero (by omega)
      have : (2 : ℕ) ∣ Nat.gcd m n := Nat.dvd_gcd hdm hdn
      rw [hcop] at this
      omega
    · exact h2
  have hnodd : n % 2 = 1 := by omega
  have hmO : Odd m := Nat.odd_iff.mpr hmodd
  have hnO : Odd n := Nat.odd_iff.mpr hnodd
  refine ⟨hmO, hnO, ?_⟩
  by_contra hcard
  push_neg at hcard
  have hcard20 : (m * n).primeFactors.card ≤ 20 := by omega
  set N := m * n with hN
  have hN0 : N ≠ 0 := by positivity
  -- σ N = (m + n + 1)^2
  have hsigmaN : σ 1 N = (m + n + 1) ^ 2 := by
    rw [hN, isMultiplicative_sigma.map_mul_of_coprime hcop, hsm, hsn]; ring
  -- every prime factor of N is odd
  have hodd : ∀ p ∈ N.primeFactors, Nat.Prime p ∧ p ≠ 2 := by
    intro p hp
    refine ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩
    rintro rfl
    have hdvd : 2 ∣ N := Nat.dvd_of_mem_primeFactors hp
    have : ¬ (2 ∣ N) := by
      rw [hN]
      intro hcon
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hcon with h2 | h2
      · omega
      · omega
    exact this hdvd
  -- the abundancy of N exceeds 4
  have hlow : (4 : ℚ) * (N : ℚ) < (σ 1 N : ℚ) := by
    rw [hsigmaN]
    have hmq : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm0
    have hnq : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn0
    have hNq : (N : ℚ) = (m : ℚ) * (n : ℚ) := by rw [hN]; push_cast; ring
    rw [hNq]
    have hcast : (((m + n + 1) ^ 2 : ℕ) : ℚ) = ((m : ℚ) + (n : ℚ) + 1) ^ 2 := by push_cast; ring
    rw [hcast]
    nlinarith [sq_nonneg ((m : ℚ) - (n : ℚ))]
  -- but the rational abundancy bound gives the reverse
  have hup : (σ 1 N : ℚ) ≤ (N : ℚ) * ∏ p ∈ N.primeFactors, primeRatio p :=
    sigma_one_le_mul_prod_primeRatio hN0
  have hlt : ∏ p ∈ N.primeFactors, primeRatio p < 4 := prod_primeRatio_lt_four hodd hcard20
  have hNpos : (0 : ℚ) < (N : ℚ) := by
    have : 0 < N := by positivity
    exact_mod_cast this
  nlinarith

/-- Complementary part of Hagis–Lord Proposition 2: the two members of a coprime
same-parity betrothed pair are perfect squares.  (Both members are odd, hence their sum
plus one is odd, so `σ` takes an odd value at each member; now apply `odd_sigma_one_iff`.) -/
theorem coprime_sameParity_isSquare {m n : ℕ} (h : Betrothed m n)
    (hcop : Nat.Coprime m n) (hpar : m % 2 = n % 2) :
    IsSquare m ∧ IsSquare n := by
  obtain ⟨hmO, hnO, -⟩ := coprime_sameParity_twentyOne_primeFactors h hcop hpar
  obtain ⟨hm0, hn0, hsm, hsn⟩ := h
  have hm2 : m % 2 = 1 := Nat.odd_iff.mp hmO
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hnO
  have hsum : Odd (m + n + 1) := Nat.odd_iff.mpr (by omega)
  constructor
  · exact (odd_sigma_one_iff (by omega) hmO).mp (by rw [hsm]; exact hsum)
  · exact (odd_sigma_one_iff (by omega) hnO).mp (by rw [hsn]; exact hsum)

/-!
## Exact theorem versus historical computational lower bounds

Everything proved above is unconditional and fully formal:

* `coprime_sameParity_twentyOne_primeFactors` — a coprime betrothed pair of equal parity
  consists of two odd numbers, and `m * n` has at least twenty-one distinct prime factors;
* `coprime_sameParity_isSquare` — such `m` and `n` are moreover perfect squares.

By contrast, statements such as "no betrothed pair of equal parity exists below a given
search bound", or numerical lower bounds for the smallest possible such pair obtained by
exhaustive computer search, are *computational* results reported in the literature.  They
are **not** formalised here, are not used anywhere in the proofs above, and no such claim is
asserted or assumed in this file.
-/

end Brockian.BetrothedNumbers

