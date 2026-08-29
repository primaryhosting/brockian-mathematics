import Mathlib

namespace Brockian.AliquotStructure

/-- Corpus definition, copied verbatim for a self-contained module. -/
def aliquot (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

/-- The sum of all divisors of `n` equals its aliquot sum plus `n` itself.
The positivity hypothesis `hn` was requested in the statement but is not needed
for the proof (for `n = 0` both sides are `0`). -/
theorem sigma_eq_aliquot_add_self {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, d = aliquot n + n :=
  Nat.sum_divisors_eq_sum_properDivisors_add_self

/-- Corpus definition, copied verbatim for a self-contained module. -/
def Semiperfect (n : ℕ) : Prop :=
  ∃ s ∈ n.properDivisors.powerset, ∑ d ∈ s, d = n

/-- A perfect number (aliquot sum equal to itself) is semiperfect: take the full
set of proper divisors as the witnessing subset.

The positivity hypothesis `hn` was requested in the statement but is not needed
for the proof. -/
theorem semiperfect_of_perfect {n : ℕ} (hn : 0 < n) (h : aliquot n = n) :
    Semiperfect n :=
  ⟨n.properDivisors, Finset.mem_powerset_self _, h⟩

/-- Corpus definition, copied verbatim for a self-contained module. -/
def sigma1 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- Corpus definition, copied verbatim for a self-contained module. -/
def Hyperperfect (k n : ℕ) : Prop := 0 < n ∧ k * sigma1 n = (k + 1) * n + (k - 1)

/-- Corpus definition, copied verbatim for a self-contained module. -/
def Perfectσ (n : ℕ) : Prop := 0 < n ∧ sigma1 n = 2 * n

theorem hyperperfect_one_iff_perfect {n : ℕ} :
    Hyperperfect 1 n ↔ Perfectσ n := by
  constructor
  · rintro ⟨hn, h⟩
    exact ⟨hn, by simpa using h⟩
  · rintro ⟨hn, h⟩
    exact ⟨hn, by simpa using h⟩

/-- Corpus definition, copied verbatim for a self-contained module. -/
def Quasiperfect (n : ℕ) : Prop := 0 < n ∧ sigma1 n = 2 * n + 1

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

/-- For an odd `p`, the geometric sum `1 + p + ⋯ + p ^ e` is odd iff `e` is even. -/
lemma even_of_odd_geom_sum {p e : ℕ} (hp : Odd p)
    (h : Odd (∑ k ∈ Finset.range (e + 1), p ^ k)) : Even e := by
  rw [Nat.odd_iff, Finset.sum_nat_mod] at h
  have hk : ∀ k ∈ Finset.range (e + 1), p ^ k % 2 = 1 := fun k _ => Nat.odd_iff.mp hp.pow
  rw [Finset.sum_congr rfl hk] at h
  simp at h
  rw [Nat.even_iff]
  omega

/-- A positive natural number all of whose prime exponents are even is a square. -/
lemma isSquare_of_factorization_even {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p, Even (n.factorization p)) : IsSquare n := by
  refine ⟨n.factorization.prod fun p k => p ^ (k / 2), ?_⟩
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  rw [← Finsupp.prod_mul]
  refine Finsupp.prod_congr fun p _ => ?_
  rw [← pow_add]
  congr 1
  obtain ⟨k, hk⟩ := h p
  omega

theorem quasiperfect_isSquare_or_two_mul_square {n : ℕ} (h : Quasiperfect n) :
    IsSquare n ∨ ∃ m : ℕ, n = 2 * m ^ 2 := by
  obtain ⟨hn, hs⟩ := h
  have hn0 : n ≠ 0 := hn.ne'
  have hodd : Odd (sigma1 n) := ⟨n, by omega⟩
  have hprod : sigma1 n =
      ∏ p ∈ n.primeFactors, ∑ k ∈ Finset.range (n.factorization p + 1), p ^ k :=
    Nat.sum_divisors hn0
  -- every odd prime occurs to an even power
  have hfac : ∀ p, p ≠ 2 → Even (n.factorization p) := by
    intro p hp2
    by_cases hmem : p ∈ n.primeFactors
    · have hdvd : (∑ k ∈ Finset.range (n.factorization p + 1), p ^ k) ∣ sigma1 n := by
        rw [hprod]; exact Finset.dvd_prod_of_mem _ hmem
      obtain ⟨c, hc⟩ := hdvd
      rw [hc] at hodd
      exact even_of_odd_geom_sum
        ((Nat.prime_of_mem_primeFactors hmem).odd_of_ne_two hp2) (Nat.odd_mul.mp hodd).1
    · have : n.factorization p = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
        exact hmem
      simp [this]
  rcases Nat.even_or_odd (n.factorization 2) with h2 | h2
  · left
    refine isSquare_of_factorization_even hn0 fun p => ?_
    by_cases hp : p = 2
    · subst hp; exact h2
    · exact hfac p hp
  · right
    have hdvd2 : 2 ∣ n := by
      have : (2:ℕ).Prime := Nat.prime_two
      have hpos : 0 < n.factorization 2 := by
        rcases h2 with ⟨k, hk⟩; omega
      exact (Nat.Prime.dvd_iff_one_le_factorization this hn0).mpr hpos
    set m := n / 2 with hm
    have hnm : n = 2 * m := (Nat.mul_div_cancel' hdvd2).symm
    have hm0 : m ≠ 0 := by
      intro h0; rw [h0] at hnm; omega
    have hmfac : ∀ p, Even (m.factorization p) := by
      intro p
      have hfd : m.factorization = n.factorization - (2:ℕ).factorization := by
        rw [hm]; exact Nat.factorization_div hdvd2
      by_cases hp : p = 2
      · subst hp
        have : m.factorization 2 = n.factorization 2 - 1 := by
          rw [hfd]; simp [Nat.Prime.factorization Nat.prime_two]
        rw [this, Nat.even_sub (by rcases h2 with ⟨k, hk⟩; omega)]
        simpa using h2
      · have : m.factorization p = n.factorization p := by
          rw [hfd]
          simp [Nat.Prime.factorization Nat.prime_two, Ne.symm hp]
        rw [this]
        exact hfac p hp
    obtain ⟨r, hr⟩ := isSquare_of_factorization_even hm0 hmfac
    exact ⟨r, by rw [hnm, hr]; ring⟩

theorem semiperfect_mul_right {n m : ℕ} (hn : 0 < n) (hm : 1 < m)
    (h : Semiperfect n) : Semiperfect (n * m) := by
  obtain ⟨s, hs, hsum⟩ := h
  rw [Finset.mem_powerset] at hs
  refine ⟨s.image (· * m), Finset.mem_powerset.2 ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    have hd' := hs hd
    rw [Nat.mem_properDivisors] at hd' ⊢
    exact ⟨mul_dvd_mul_right hd'.1 m, by
      exact Nat.mul_lt_mul_of_lt_of_le hd'.2 le_rfl (by omega)⟩
  · rw [Finset.sum_image
      (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_right (by omega) hab),
      ← Finset.sum_mul, hsum]

/-- If the aliquot sum of `n` is less than `n` (i.e. `n` is deficient), then no subset of
the proper divisors of `n` can sum to `n`, so `n` is not semiperfect. -/
theorem not_semiperfect_of_aliquot_lt {n : ℕ} (h : aliquot n < n) :
    ¬ Semiperfect n := by
  rintro ⟨s, hs, hsum⟩
  rw [Finset.mem_powerset] at hs
  have hle : ∑ d ∈ s, d ≤ ∑ d ∈ n.properDivisors, d :=
    Finset.sum_le_sum_of_subset (f := fun d => d) hs
  rw [hsum] at hle
  exact absurd (hle.trans_lt h) (lt_irrefl n)

/-- No prime is quasiperfect: for a prime `p`, `sigma1 p = 1 + p < 2 * p + 1`. -/
theorem not_quasiperfect_prime {p : ℕ} (hp : Nat.Prime p) :
    ¬ Quasiperfect p := by
  rintro ⟨hpos, hsum⟩
  rw [sigma1, hp.divisors, Finset.sum_pair hp.one_lt.ne] at hsum
  omega

/-- A `k`-hyperperfect number (for `k ≥ 1`) is either `1` or at least `3`;
the only case to rule out is `n = 2`, where `sigma1 2 = 3` gives `3k = 3k + 1`.
(The hypothesis `1 ≤ k` is part of the requested statement but is not needed.) -/
theorem hyperperfect_pos_of_hyperperfect {k n : ℕ} (hk : 1 ≤ k)
    (h : Hyperperfect k n) : n = 1 ∨ 3 ≤ n := by
  obtain ⟨hn, he⟩ := h
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · interval_cases n
    · left; rfl
    · exfalso
      have h2 : sigma1 2 = 3 := by decide
      rw [h2] at he
      omega
  · right; exact h3

end Brockian.AliquotStructure
