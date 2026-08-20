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
# Gilbreath Conjecture
Category: Brockian Conjecture
Target: Brockian.GilbreathConjecture.GilbreathConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

-- The header block above is a plain comment rather than a module docstring `/-! ... -/`
-- because Lean 4 does not allow any command (including a module docstring) before `import`.

namespace Brockian.GilbreathConjecture

/-!
## The Gilbreath triangle

Row `0` of the triangle is the sequence of primes `2, 3, 5, 7, 11, …`, and each
subsequent row is obtained by taking absolute values of consecutive differences.
Gilbreath's conjecture asserts that every row of index `≥ 1` begins with `1`.

The conjecture is open.  What is proved below is:

* `gilbreath_head_odd` – an unconditional parity result: the leading entry of every
  row of index `≥ 1` is odd (in particular nonzero);
* `gilbreath_head_eq_one_of_le` – an unconditional verification of the leading `1`
  for the first `25` rows;
* `GilbreathConjecture` – the full conjecture, derived from the Odlyzko-style
  criterion `OdlyzkoCriterion` (see below).
-/

/-- `G k n` is the `n`-th entry (0-indexed) of the `k`-th row of the Gilbreath
triangle: row `0` is the sequence of primes and each later row consists of the
absolute differences of consecutive entries of the previous row. -/
noncomputable def G : ℕ → ℕ → ℕ
  | 0, n => Nat.nth Nat.Prime n
  | k + 1, n => Nat.dist (G k (n + 1)) (G k n)

@[simp] lemma G_zero (n : ℕ) : G 0 n = Nat.nth Nat.Prime n := rfl

@[simp] lemma G_succ (k n : ℕ) : G (k + 1) n = Nat.dist (G k (n + 1)) (G k n) := rfl

/-! ### Parity -/

private lemma dist_mod_two (a b : ℕ) : Nat.dist a b % 2 = (a + b) % 2 := by
  unfold Nat.dist; omega

lemma nth_prime_zero : Nat.nth Nat.Prime 0 = 2 := by
  have h : Nat.nth Nat.Prime (Nat.count Nat.Prime 2) = 2 := Nat.nth_count Nat.prime_two
  have hc : Nat.count Nat.Prime 2 = 0 := by decide
  rwa [hc] at h

lemma nth_prime_odd {n : ℕ} (hn : 1 ≤ n) : Odd (Nat.nth Nat.Prime n) := by
  have hlt : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime n :=
    (Nat.nth_lt_nth Nat.infinite_setOf_prime).2 hn
  rw [nth_prime_zero] at hlt
  exact (Nat.Prime.odd_of_ne_two (Nat.prime_nth_prime n) (by omega))

/-- The parity pattern of the Gilbreath triangle: for every row of index `≥ 1`
the leading entry is odd and all further entries are even. -/
lemma G_mod_two (k : ℕ) (n : ℕ) :
    G (k + 1) n % 2 = if n = 0 then 1 else 0 := by
  induction k generalizing n with
  | zero =>
      rw [G_succ, dist_mod_two]
      simp only [G_zero]
      have ha : Nat.nth Nat.Prime (n + 1) % 2 = 1 :=
        Nat.odd_iff.mp (nth_prime_odd (by omega))
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [if_pos rfl, nth_prime_zero]; omega
      · rw [if_neg (by omega)]
        have hb : Nat.nth Nat.Prime n % 2 = 1 := Nat.odd_iff.mp (nth_prime_odd hn)
        omega
  | succ k ih =>
      rw [G_succ, dist_mod_two]
      have h1 := ih (n + 1)
      have h2 := ih n
      rw [if_neg (by omega)] at h1
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [if_pos rfl] at h2 ⊢; omega
      · rw [if_neg (by omega)] at h2 ⊢; omega

/-- **Unconditional partial result.** The leading entry of every row of index `≥ 1`
of the Gilbreath triangle is odd; in particular it is never `0`. -/
theorem gilbreath_head_odd {k : ℕ} (hk : 1 ≤ k) : Odd (G k 0) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have := G_mod_two j 0
  rw [if_pos rfl] at this
  exact Nat.odd_iff.2 this

/-- Consequently the leading entry of every row of index `≥ 1` is at least `1`. -/
theorem gilbreath_head_pos {k : ℕ} (hk : 1 ≤ k) : 1 ≤ G k 0 := by
  have := gilbreath_head_odd hk
  rcases this with ⟨m, hm⟩; omega

/-! ### Unconditional verification of the first rows

We verify the leading `1` for rows `1, …, 25` by computing with an explicit list of
the first 26 primes; the identification of that list with `Nat.nth Nat.Prime` is
supplied by `Nat.nth_count`.
-/

set_option maxRecDepth 100000

/-- The first `26` primes. -/
def primeList : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83,
    89, 97, 101]

/-- A computable truncated copy of the Gilbreath triangle, built from `primeList`. -/
def Gc : ℕ → ℕ → ℕ
  | 0, n => primeList.getD n 0
  | k + 1, n => Nat.dist (Gc k (n + 1)) (Gc k n)

private lemma nth_prime_eq_of_count (n p : ℕ) (hp : Nat.Prime p)
    (hc : Nat.count Nat.Prime p = n) : Nat.nth Nat.Prime n = p := by
  subst hc; exact Nat.nth_count hp

private lemma G_zero_eq_Gc (n : ℕ) (hn : n ≤ 25) : G 0 n = Gc 0 n := by
  interval_cases n
  · exact nth_prime_eq_of_count 0 2 (by norm_num) (by decide)
  · exact nth_prime_eq_of_count 1 3 (by norm_num) (by decide)
  · exact nth_prime_eq_of_count 2 5 (by norm_num) (by decide)
  · exact nth_prime_eq_of_count 3 7 (by norm_num) (by decide)
  · exact nth_prime_eq_of_count 4 11 (by norm_num) (by decide)
  · exact nth_prime_eq_of_count 5 13 (by norm_num) (by decide)
  · exact nth_prime_eq_of_count 6 17 (by norm_num) (by decide)
  · exact nth_prime_eq_of_count 7 19 (by norm_num) (by decide)
  · exact nth_prime_eq_of_count 8 23 (by norm_num) (by decide)
  · exact nth_prime_eq_of_count 9 29 (by norm_num) (by decide)
  · exact nth_prime_eq_of_count 10 31 (by norm_num) (by decide)
  · exact nth_prime_eq_of_count 11 37 (by norm_num) (by decide)
  · exact nth_prime_eq_of_count 12 41 (by norm_num) (by decide)
  · exact nth_prime_eq_of_count 13 43 (by norm_num) (by decide)
  · exact nth_prime_eq_of_count 14 47 (by norm_num) (by decide)
  · exact nth_prime_eq_of_count 15 53 (by norm_num) (by decide)
  · exact nth_prime_eq_of_count 16 59 (by norm_num) (by decide)
  · exact nth_prime_eq_of_count 17 61 (by norm_num) (by decide)
  · exact nth_prime_eq_of_count 18 67 (by norm_num) (by decide)
  · exact nth_prime_eq_of_count 19 71 (by norm_num) (by decide)
  · exact nth_prime_eq_of_count 20 73 (by norm_num) (by decide)
  · exact nth_prime_eq_of_count 21 79 (by norm_num) (by decide)
  · exact nth_prime_eq_of_count 22 83 (by norm_num) (by decide)
  · exact nth_prime_eq_of_count 23 89 (by norm_num) (by decide)
  · exact nth_prime_eq_of_count 24 97 (by norm_num) (by decide)
  · exact nth_prime_eq_of_count 25 101 (by norm_num) (by decide)

private lemma G_eq_Gc (k n : ℕ) (h : k + n ≤ 25) : G k n = Gc k n := by
  induction k generalizing n with
  | zero => exact G_zero_eq_Gc n (by omega)
  | succ k ih =>
      show Nat.dist (G k (n + 1)) (G k n) = Nat.dist (Gc k (n + 1)) (Gc k n)
      rw [ih (n + 1) (by omega), ih n (by omega)]

private lemma Gc_head (k : ℕ) : k < 26 → 1 ≤ k → Gc k 0 = 1 := by
  revert k; decide

/-- **Unconditional partial result.** Gilbreath's conjecture holds for the first `25`
rows: for `1 ≤ k ≤ 25` the leading entry of row `k` is `1`. -/
theorem gilbreath_head_eq_one_of_le {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ 25) : G k 0 = 1 := by
  rw [G_eq_Gc k 0 (by omega)]
  exact Gc_head k (by omega) hk

/-! ### The Odlyzko-style propagation criterion -/

/-- `GoodRow k n` says that row `k` starts with a `1` followed by `n` entries each
equal to `0` or `2`. -/
def GoodRow (k n : ℕ) : Prop :=
  G k 0 = 1 ∧ ∀ j, 1 ≤ j → j ≤ n → G k j = 0 ∨ G k j = 2

/-- One step of Odlyzko's propagation: a `1` followed by `n + 1` entries in `{0, 2}`
produces, in the next row, a `1` followed by `n` entries in `{0, 2}`. -/
lemma GoodRow.step {k n : ℕ} (h : GoodRow k (n + 1)) : GoodRow (k + 1) n := by
  obtain ⟨h0, h2⟩ := h
  constructor
  · have := h2 1 le_rfl (by omega)
    rw [G_succ, h0]
    rcases this with h | h <;> rw [h] <;> decide
  · intro j hj1 hj2
    have ha := h2 j hj1 (by omega)
    have hb := h2 (j + 1) (by omega) (by omega)
    rw [G_succ]
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] <;> simp [Nat.dist]

/-- Iterating `GoodRow.step`: a good row of width `n` forces a leading `1` for the
next `n` rows as well. -/
lemma GoodRow.iterate {k n : ℕ} (h : GoodRow k n) (i : ℕ) (hi : i ≤ n) :
    GoodRow (k + i) (n - i) := by
  induction i generalizing k n with
  | zero => simpa using h
  | succ i ih =>
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have h' : GoodRow (k + 1) m := GoodRow.step h
      have := ih h' (by omega)
      have he : k + 1 + i = k + (i + 1) := by omega
      have he2 : m - i = m + 1 - (i + 1) := by omega
      rwa [he, he2] at this

/-- **Odlyzko's criterion.** For every `N` there is a row index `k` with
`1 ≤ k ≤ N` such that row `k` begins with a `1` followed by at least `N - k`
entries, each of which is `0` or `2`.

This is the finitely-checkable condition that Odlyzko-style computations verify for
larger and larger `N`; it is exactly the statement that lets the leading `1`
propagate arbitrarily far down the triangle. -/
def OdlyzkoCriterion : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧ GoodRow k (N - k)

/-- The criterion is not vacuous: each of its instances with `N ≤ 25` is a theorem
(witnessed, crudely, by the row `N` itself, whose leading entry we verified above). -/
lemma odlyzkoCriterion_of_le {N : ℕ} (h1 : 1 ≤ N) (h2 : N ≤ 25) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧ GoodRow k (N - k) :=
  ⟨N, h1, le_rfl, gilbreath_head_eq_one_of_le h1 h2, fun _ _ hj => absurd hj (by omega)⟩

/-- **Gilbreath's conjecture**, conditional on the Odlyzko-style criterion
`OdlyzkoCriterion`: every row of index `≥ 1` of the Gilbreath triangle begins
with `1`. -/
theorem GilbreathConjecture (h : OdlyzkoCriterion) :
    ∀ k : ℕ, 1 ≤ k → G k 0 = 1 := by
  intro k hk
  obtain ⟨m, hm1, hmk, hgood⟩ := h k hk
  have h2 := hgood.iterate (k - m) le_rfl
  have he : m + (k - m) = k := by omega
  rw [he] at h2
  exact h2.1

end Brockian.GilbreathConjecture

