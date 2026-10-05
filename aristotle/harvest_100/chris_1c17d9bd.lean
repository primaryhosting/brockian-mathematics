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
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Overview

(The requested header appears at the very top of this file as a plain block comment rather than
as a module docstring, because Lean requires every `import` to precede any module docstring.)

A *Ruth–Aaron pair* is a pair of consecutive integers `(n, n+1)` with the same sum of prime
factors counted with multiplicity (`sopfr`), e.g. `(714, 715)`: `714 = 2·3·7·17` and
`715 = 5·11·13`, both with factor sum `29`.

Whether there are infinitely many Ruth–Aaron pairs is an open problem (Erdős conjectured that
there are).  This file contains:

* the basic theory of `sopfr` (additivity, `sopfr n ≤ n`, value at primes);
* verification of the first Ruth–Aaron pairs `5, 8, 15, 77, 125, 714`;
* two *unconditional* partial results: `sopfr n - sopfr (n+1)` is positive infinitely often and
  negative infinitely often, i.e. the difference changes sign infinitely often (a Ruth–Aaron pair
  is exactly a place where the difference vanishes);
* an *unconditional* structural obstruction, `no_prime_semiprime_pair` /
  `not_isRuthAaronPair_of_semiprimes`: no Ruth–Aaron pair consists of two semiprimes, i.e.
  `p * q + 1 = r * s` together with `p + q = r + s` is impossible for primes `p, q, r, s`
  (this rules out the simplest conceivable parametric families);
* a *conditional reduction*: `RuthAaronInfinitude` derives the infinitude of Ruth–Aaron pairs
  from `PrimeFactorizationHypothesis`, a statement phrased purely in terms of lists of primes
  (arbitrarily large products of primes `L` whose product is one less than the product of a list
  `M` of primes with the same sum), with no reference to the factorization function.
  `ruthAaron_infinite_iff` shows that the reduction loses nothing: the hypothesis is in fact
  equivalent to the infinitude statement.
-/

namespace Brockian.RuthAaronPairs

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity.
By convention `sopfr 0 = sopfr 1 = 0`. -/
def sopfr (n : ℕ) : ℕ := (Nat.primeFactorsList n).sum

/-- `n` starts a Ruth–Aaron pair when `n ≥ 2` and `n` and `n + 1` have the same sum of prime
factors, counted with multiplicity. -/
def IsRuthAaronPair (n : ℕ) : Prop := 2 ≤ n ∧ sopfr n = sopfr (n + 1)

/-- The set of Ruth–Aaron numbers, i.e. of left endpoints of Ruth–Aaron pairs. -/
def RuthAaronSet : Set ℕ := {n | IsRuthAaronPair n}

/-! ### Basic properties of `sopfr` -/

@[simp] lemma sopfr_zero : sopfr 0 = 0 := by simp [sopfr]

@[simp] lemma sopfr_one : sopfr 1 = 0 := by simp [sopfr]

/-- The sum of prime factors of a product of a list of primes is the sum of that list. -/
lemma sopfr_prod_of_primes {L : List ℕ} (hL : ∀ p ∈ L, p.Prime) : sopfr L.prod = L.sum :=
  ((Nat.primeFactorsList_unique (n := L.prod) rfl hL).sum_eq).symm

@[simp] lemma sopfr_prime {p : ℕ} (hp : p.Prime) : sopfr p = p := by
  simp [sopfr, Nat.primeFactorsList_prime hp]

/-- `sopfr` turns multiplication into addition. -/
lemma sopfr_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : sopfr (a * b) = sopfr a + sopfr b := by
  have h := Nat.perm_primeFactorsList_mul ha hb
  simp [sopfr, h.sum_eq]

/-- Any list of naturals all of which are at least `2` has sum at most its product. -/
lemma list_sum_le_prod {L : List ℕ} (hL : ∀ x ∈ L, 2 ≤ x) : L.sum ≤ L.prod := by
  induction L with
  | nil => simp
  | cons a l ih =>
      have ha : 2 ≤ a := hL a (by simp)
      have hl : ∀ x ∈ l, 2 ≤ x := fun x hx => hL x (by simp [hx])
      have hsum := ih hl
      rcases l with _ | ⟨b, l'⟩
      · simp
      · have hb : 2 ≤ b := hl b (by simp)
        have hprod : 2 ≤ (b :: l').prod := by
          have h1 : 1 ≤ l'.prod := Nat.one_le_iff_ne_zero.mpr <| by
            intro h
            have h0 : (0 : ℕ) ∈ l' := List.prod_eq_zero_iff.mp h
            exact absurd (hl 0 (by simp [h0])) (by norm_num)
          calc 2 = 2 * 1 := by ring
            _ ≤ b * l'.prod := Nat.mul_le_mul hb h1
            _ = (b :: l').prod := by simp
        simp only [List.sum_cons, List.prod_cons] at *
        nlinarith

/-- The sum of the prime factors of `n` (with multiplicity) is at most `n`. -/
lemma sopfr_le_self (n : ℕ) : sopfr n ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hprod : (Nat.primeFactorsList n).prod = n := Nat.prod_primeFactorsList hn.ne'
    have := list_sum_le_prod (L := Nat.primeFactorsList n)
      (fun x hx => (Nat.prime_of_mem_primeFactorsList hx).two_le)
    simpa [sopfr, hprod] using this

/-! ### Examples of Ruth–Aaron pairs -/

/-- A convenient way of computing `sopfr` at an explicitly factored number. -/
lemma sopfr_eq_of_factorization {n : ℕ} {L : List ℕ} (hL : ∀ p ∈ L, p.Prime)
    (hprod : L.prod = n) : sopfr n = L.sum := by
  subst hprod; exact sopfr_prod_of_primes hL

/-- The Ruth–Aaron pair `(5, 6)`. -/
theorem isRuthAaronPair_5 : IsRuthAaronPair 5 := by
  refine ⟨by norm_num, ?_⟩
  rw [sopfr_eq_of_factorization (L := [5]) (by decide) (by norm_num),
    sopfr_eq_of_factorization (L := [2, 3]) (by decide) (by norm_num)]
  decide

/-- The Ruth–Aaron pair `(8, 9)`. -/
theorem isRuthAaronPair_8 : IsRuthAaronPair 8 := by
  refine ⟨by norm_num, ?_⟩
  rw [sopfr_eq_of_factorization (L := [2, 2, 2]) (by decide) (by norm_num),
    sopfr_eq_of_factorization (L := [3, 3]) (by decide) (by norm_num)]
  decide

/-- The Ruth–Aaron pair `(15, 16)`. -/
theorem isRuthAaronPair_15 : IsRuthAaronPair 15 := by
  refine ⟨by norm_num, ?_⟩
  rw [sopfr_eq_of_factorization (L := [3, 5]) (by decide) (by norm_num),
    sopfr_eq_of_factorization (L := [2, 2, 2, 2]) (by decide) (by norm_num)]
  decide

/-- The Ruth–Aaron pair `(77, 78)`. -/
theorem isRuthAaronPair_77 : IsRuthAaronPair 77 := by
  refine ⟨by norm_num, ?_⟩
  rw [sopfr_eq_of_factorization (L := [7, 11]) (by decide) (by norm_num),
    sopfr_eq_of_factorization (L := [2, 3, 13]) (by decide) (by norm_num)]
  decide

/-- The Ruth–Aaron pair `(125, 126)`. -/
theorem isRuthAaronPair_125 : IsRuthAaronPair 125 := by
  refine ⟨by norm_num, ?_⟩
  rw [sopfr_eq_of_factorization (L := [5, 5, 5]) (by decide) (by norm_num),
    sopfr_eq_of_factorization (L := [2, 3, 3, 7]) (by decide) (by norm_num)]
  decide

/-- The classical Ruth–Aaron pair `(714, 715)`. -/
theorem isRuthAaronPair_714 : IsRuthAaronPair 714 := by
  refine ⟨by norm_num, ?_⟩
  rw [sopfr_eq_of_factorization (L := [2, 3, 7, 17]) (by decide) (by norm_num),
    sopfr_eq_of_factorization (L := [5, 11, 13]) (by decide) (by norm_num)]
  decide

/-! ### Unconditional partial results: the difference changes sign infinitely often -/

/-- For `2 ≤ m`, the sum of prime factors of `2 * m` is smaller than `2 * m + 1`. -/
lemma sopfr_two_mul_lt {m : ℕ} (hm : 2 ≤ m) : sopfr (2 * m) < 2 * m + 1 := by
  have h : sopfr (2 * m) = 2 + sopfr m := by
    rw [sopfr_mul (by norm_num) (by omega)]
    simp [sopfr_prime Nat.prime_two]
  have := sopfr_le_self m
  omega

/-- Every prime `p ≥ 7` is of the form `2 * m + 1` with `3 ≤ m`. -/
lemma odd_prime_form {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) : ∃ m, 3 ≤ m ∧ p = 2 * m + 1 := by
  have hodd : ¬ 2 ∣ p := fun h =>
    absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h) (by omega)
  rcases Nat.even_or_odd p with he | ho
  · exact absurd he.two_dvd hodd
  · obtain ⟨m, hm⟩ := ho
    exact ⟨m, by omega, hm⟩

/-- There are infinitely many `n` with `sopfr (n + 1) < sopfr n`. -/
theorem infinite_sopfr_succ_lt : {n : ℕ | sopfr (n + 1) < sopfr n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (max (N + 1) 7)
  have hp7 : 7 ≤ p := le_trans (le_max_right _ _) hpN
  have hpN' : N < p := lt_of_lt_of_le (by omega) (le_trans (le_max_left _ _) hpN)
  obtain ⟨m, hm3, hm⟩ := odd_prime_form hp hp7
  refine ⟨p, ?_, hpN'⟩
  have h1 : sopfr p = p := sopfr_prime hp
  have h2 : p + 1 = 2 * (m + 1) := by omega
  have h4 : sopfr (p + 1) = 2 + sopfr (m + 1) := by
    rw [h2, sopfr_mul (by norm_num) (by omega)]
    simp [sopfr_prime Nat.prime_two]
  have h5 := sopfr_le_self (m + 1)
  simp only [Set.mem_setOf_eq, h1]
  omega

/-- There are infinitely many `n` with `sopfr n < sopfr (n + 1)`. -/
theorem infinite_sopfr_lt_succ : {n : ℕ | sopfr n < sopfr (n + 1)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (max (N + 2) 7)
  have hp7 : 7 ≤ p := le_trans (le_max_right _ _) hpN
  have hpN' : N + 1 < p := lt_of_lt_of_le (by omega) (le_trans (le_max_left _ _) hpN)
  obtain ⟨m, hm3, hm⟩ := odd_prime_form hp hp7
  refine ⟨2 * m, ?_, by omega⟩
  have h2 : sopfr (2 * m + 1) = p := by rw [← hm]; exact sopfr_prime hp
  have h3 : sopfr (2 * m) < 2 * m + 1 := sopfr_two_mul_lt (by omega)
  simp only [Set.mem_setOf_eq, h2]
  omega

/-! ### A structural obstruction: no Ruth–Aaron pair of two semiprimes -/

/-- The only way two squares of naturals can differ by `4` is `4 = 4 + 0`. -/
lemma sq_eq_sq_add_four {u v : ℕ} (h : u ^ 2 = v ^ 2 + 4) : u = 2 ∧ v = 0 := by
  have huv : v < u := by nlinarith
  have h1 : (v + 1) ^ 2 ≤ u ^ 2 := Nat.pow_le_pow_left huv 2
  have hv : v ≤ 1 := by nlinarith
  have hu : u ≤ 3 := by nlinarith
  interval_cases u <;> interval_cases v <;> omega

/-- There are no primes `p, q, r, s` with `p * q + 1 = r * s` and `p + q = r + s`.

Equivalently (see `not_isRuthAaronPair_of_semiprimes`): no Ruth–Aaron pair consists of two
semiprimes.  The reason is rigid: the hypotheses force `(p-q)^2 = (r-s)^2 + 4`, hence `r = s` and
`{p, q} = {r-1, r+1}`, so `r-1, r, r+1` would all have to be prime. -/
theorem no_prime_semiprime_pair {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hs : s.Prime) (h1 : p * q + 1 = r * s) (h2 : p + q = r + s) : False := by
  have h1' : (p : ℤ) * q + 1 = (r : ℤ) * s := by exact_mod_cast h1
  have h2' : (p : ℤ) + q = (r : ℤ) + s := by exact_mod_cast h2
  have H : ((p : ℤ) - q) ^ 2 = ((r : ℤ) - s) ^ 2 + 4 := by
    linear_combination ((p : ℤ) + q + r + s) * h2' - 4 * h1'
  have HN : (((p : ℤ) - q).natAbs) ^ 2 = (((r : ℤ) - s).natAbs) ^ 2 + 4 := by
    zify [Int.natAbs_sq, sq_abs]
    simpa [Int.natAbs_sq, sq_abs] using H
  obtain ⟨hU, hV⟩ := sq_eq_sq_add_four HN
  have hrs : r = s := by
    have : ((r : ℤ) - s) = 0 := Int.natAbs_eq_zero.mp hV
    omega
  subst hrs
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hr2 := hr.two_le
  have key : (p = r - 1 ∧ q = r + 1) ∨ (q = r - 1 ∧ p = r + 1) := by omega
  have hrp1 : (r + 1).Prime := by
    rcases key with ⟨_, h4⟩ | ⟨_, h4⟩
    · exact h4 ▸ hq
    · exact h4 ▸ hp
  have hr2' : r = 2 := by
    rcases Nat.even_or_odd r with he | ho
    · exact (Nat.Prime.even_iff hr).mp he
    · have he2 : Even (r + 1) := ho.add_one
      have := (Nat.Prime.even_iff hrp1).mp he2
      omega
  subst hr2'
  rcases key with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega

/-- No Ruth–Aaron pair `(n, n+1)` has both `n` and `n + 1` a product of exactly two primes. -/
theorem not_isRuthAaronPair_of_semiprimes {n p q r s : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hs : s.Prime) (hn : n = p * q) (hn1 : n + 1 = r * s) :
    ¬ IsRuthAaronPair n := by
  rintro ⟨-, hRA⟩
  have e1 : sopfr n = p + q := by
    rw [hn, sopfr_mul hp.pos.ne' hq.pos.ne', sopfr_prime hp, sopfr_prime hq]
  have e2 : sopfr (n + 1) = r + s := by
    rw [hn1, sopfr_mul hr.pos.ne' hs.pos.ne', sopfr_prime hr, sopfr_prime hs]
  refine no_prime_semiprime_pair hp hq hr hs ?_ (by omega)
  rw [← hn, hn1]

/-! ### The conditional reduction -/

/-- **Prime factorization hypothesis.**  For every bound `N` there are two lists of primes `L`
and `M` such that the product of `L` exceeds `N`, the product of `M` is one more than the product
of `L`, and the two lists have the same sum.

This is a statement purely about primes: no factorization function occurs in it. -/
def PrimeFactorizationHypothesis : Prop :=
  ∀ N : ℕ, ∃ L M : List ℕ, (∀ p ∈ L, p.Prime) ∧ (∀ p ∈ M, p.Prime) ∧
    N < L.prod ∧ M.prod = L.prod + 1 ∧ L.sum = M.sum

/-- **Conditional Ruth–Aaron infinitude.**  Granting `PrimeFactorizationHypothesis`, there are
infinitely many Ruth–Aaron pairs. -/
theorem RuthAaronInfinitude (H : PrimeFactorizationHypothesis) : RuthAaronSet.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨L, M, hL, hM, hgt, hprod, hsum⟩ := H (N + 2)
  refine ⟨L.prod, ⟨by omega, ?_⟩, by omega⟩
  have h1 : sopfr L.prod = L.sum := sopfr_prod_of_primes hL
  have h2 : sopfr (L.prod + 1) = M.sum := by
    rw [← hprod]; exact sopfr_prod_of_primes hM
  rw [h1, h2, hsum]

/-- Conversely, the infinitude of Ruth–Aaron pairs implies `PrimeFactorizationHypothesis`. -/
theorem primeFactorizationHypothesis_of_infinite (h : RuthAaronSet.Infinite) :
    PrimeFactorizationHypothesis := by
  intro N
  obtain ⟨n, hn, hNn⟩ := h.exists_gt N
  obtain ⟨hn2, hn3⟩ := hn
  refine ⟨n.primeFactorsList, (n + 1).primeFactorsList,
    fun p hp => Nat.prime_of_mem_primeFactorsList hp,
    fun p hp => Nat.prime_of_mem_primeFactorsList hp, ?_, ?_, hn3⟩
  · rw [Nat.prod_primeFactorsList (by omega)]; exact hNn
  · rw [Nat.prod_primeFactorsList (by omega), Nat.prod_primeFactorsList (by omega)]

/-- A concrete sufficient condition, of the shape realised by the pair `(77, 78)`
(`77 = 7 · 11`, `78 = 2 · 3 · 13`, `7 + 11 = 2 + 3 + 13`): arbitrarily large products of two
primes `p * q` such that `p * q + 1 = 2 * r * s` with `r, s` prime and `p + q = 2 + r + s`. -/
theorem ruthAaron_infinite_of_prime_quadruples
    (H : ∀ N : ℕ, ∃ p q r s : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧
      N < p * q ∧ p * q + 1 = 2 * (r * s) ∧ p + q = 2 + r + s) :
    RuthAaronSet.Infinite := by
  refine RuthAaronInfinitude (fun N => ?_)
  obtain ⟨p, q, r, s, hp, hq, hr, hs, hN, hprod, hsum⟩ := H N
  refine ⟨[p, q], [2, r, s], ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption
  · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    exacts [Nat.prime_two, hr, hs]
  · simpa using hN
  · simp only [List.prod_cons, List.prod_nil, mul_one]
    rw [← hprod]
  · simp only [List.sum_cons, List.sum_nil, add_zero]
    omega

/-- The reduction is faithful: the infinitude of Ruth–Aaron pairs is *equivalent* to the
purely prime-theoretic `PrimeFactorizationHypothesis`. -/
theorem ruthAaron_infinite_iff : RuthAaronSet.Infinite ↔ PrimeFactorizationHypothesis :=
  ⟨primeFactorizationHypothesis_of_infinite, RuthAaronInfinitude⟩

end Brockian.RuthAaronPairs

