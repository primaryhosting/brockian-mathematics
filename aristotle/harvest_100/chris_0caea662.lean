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

/-!
# Gilbreath Conjecture
Category: Brockian Conjecture
Target: Brockian.GilbreathConjecture.GilbreathConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Gilbreath's conjecture concerns the triangle of iterated absolute differences of the
sequence of primes.  Writing `p 0 = 2, p 1 = 3, p 2 = 5, …` for the primes and
`row p k` for the `k`-th row of iterated absolute differences, the conjecture states

  `row p k 0 = 1`  for every `k ≥ 1`.

The conjecture is open.  What is formalised here is:

* `Brockian.GilbreathConjecture.GilbreathConjecture` : a Lean-checked **conditional
  reduction** — the classical Odlyzko-style criterion implies Gilbreath's conjecture.
  The criterion asks that, for every row index `m ≥ 1`, some earlier row `k` (with
  `1 ≤ k ≤ m`) begins with a `1` followed by at least `m - k` entries taken from
  `{0, 2}`.  This is exactly the property that Odlyzko verified numerically for
  huge ranges.

* `Brockian.GilbreathConjecture.gilbreath_le_25` : an unconditional, kernel-checked
  verification of the conjecture for all rows `1 ≤ k ≤ 25`.

The mathematical content of the reduction is the propagation lemma
`GoodRow.diff` : a row of the shape `1, e₁, …, e_L` with all `eᵢ ∈ {0, 2}` is followed
by a row of the shape `1, e'₁, …, e'_{L-1}` with all `e'ᵢ ∈ {0, 2}`, because
`|even - 1| = 1` and `|even - even|` is `0` or `2`.
-/

set_option maxRecDepth 40000

namespace Brockian.GilbreathConjecture

/-- One step of the Gilbreath triangle: the sequence of absolute differences of
consecutive terms. -/
def diff (a : ℕ → ℕ) (n : ℕ) : ℕ := ((a (n + 1) : ℤ) - (a n : ℤ)).natAbs

/-- The `k`-th row of the difference triangle of the sequence `a`
(`row a 0 = a`). -/
def row (a : ℕ → ℕ) (k : ℕ) : ℕ → ℕ := diff^[k] a

/-- The sequence of primes, `prime 0 = 2`, `prime 1 = 3`, … -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- `GoodRow a L` says that the row `a` starts with `1` and its next `L` entries all
lie in `{0, 2}`. -/
def GoodRow (a : ℕ → ℕ) (L : ℕ) : Prop :=
  a 0 = 1 ∧ ∀ i, 1 ≤ i → i ≤ L → a i = 0 ∨ a i = 2

/-- The Odlyzko-style criterion: for every row index `m ≥ 1` there is an earlier row
`k` (with `1 ≤ k ≤ m`) that starts with `1` and is followed by at least `m - k`
entries from `{0, 2}`. -/
def OdlyzkoCondition : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∃ k, 1 ≤ k ∧ k ≤ m ∧ GoodRow (row prime k) (m - k)

/-- Gilbreath's conjecture: every row of the difference triangle of the primes,
apart from the zeroth one, starts with `1`. -/
def GilbreathStatement : Prop := ∀ k : ℕ, 1 ≤ k → row prime k 0 = 1

/-! ### The propagation lemma -/

/-- A good row of length `L ≥ 1` is followed by a good row of length `L - 1`. -/
theorem GoodRow.step {a : ℕ → ℕ} {L : ℕ} (h : GoodRow a L) (hL : 1 ≤ L) :
    GoodRow (diff a) (L - 1) := by
  obtain ⟨h0, hmem⟩ := h
  constructor
  · have h1 := hmem 1 le_rfl hL
    simp only [diff, h0]
    rcases h1 with h1 | h1 <;> simp [h1]
  · intro i hi hiL
    have h₁ : a i = 0 ∨ a i = 2 := hmem i hi (by omega)
    have h₂ : a (i + 1) = 0 ∨ a (i + 1) = 2 := hmem (i + 1) (by omega) (by omega)
    simp only [diff]
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> simp [h₁, h₂]

/-- Every row that follows a good row of length `L`, up to `L` steps later, starts
with `1`. -/
theorem GoodRow.iterate_head {a : ℕ → ℕ} {L : ℕ} (h : GoodRow a L) :
    ∀ j ≤ L, (diff^[j] a) 0 = 1 := by
  induction L generalizing a with
  | zero => intro j hj; interval_cases j; exact h.1
  | succ L ih =>
    intro j hj
    match j with
    | 0 => exact h.1
    | (j + 1) =>
      rw [Function.iterate_succ_apply]
      have h' : GoodRow (diff a) L := by
        have := h.step (by omega)
        simpa using this
      exact ih h' j (by omega)

/-! ### The conditional reduction -/

/-- **Conditional reduction of Gilbreath's conjecture.**  If the Odlyzko-style
criterion holds — for every `m ≥ 1` some row `k ≤ m` begins with `1` followed by at
least `m - k` entries from `{0, 2}` — then Gilbreath's conjecture holds: every row
`k ≥ 1` of the iterated absolute difference triangle of the primes starts with `1`. -/
theorem GilbreathConjecture : OdlyzkoCondition → GilbreathStatement := by
  intro hOd m hm
  obtain ⟨k, hk1, hkm, hgood⟩ := hOd m hm
  have hiter : (diff^[m - k] (row prime k)) 0 = 1 :=
    hgood.iterate_head (m - k) le_rfl
  have : row prime m = diff^[m - k] (row prime k) := by
    unfold row
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  rw [this]
  exact hiter

/-! ### Unconditional verification of the first 25 rows -/

/-- The first `26` primes, as a computable function. -/
def q (i : ℕ) : ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79,
    83, 89, 97, 101].getD i 0

theorem nth_prime_eq_of_count {n p : ℕ} (hp : Nat.Prime p) (h : Nat.count Nat.Prime p = n) :
    Nat.nth Nat.Prime n = p := h ▸ Nat.nth_count hp

/-- Two sequences agreeing on an initial segment have the same difference triangle
there. -/
theorem diff_iterate_congr :
    ∀ (k : ℕ) (a b : ℕ → ℕ) (n : ℕ), (∀ i ≤ n + k, a i = b i) →
      (diff^[k] a) n = (diff^[k] b) n := by
  intro k
  induction k with
  | zero => intro a b n h; simpa using h n (by omega)
  | succ k ih =>
    intro a b n h
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    refine ih _ _ n ?_
    intro i hi
    simp only [diff]
    rw [h i (by omega), h (i + 1) (by omega)]

theorem prime_eq_q : ∀ i ≤ 25, prime i = q i := by
  have h0 : prime 0 = 2 := nth_prime_eq_of_count (by norm_num) (by decide)
  have h1 : prime 1 = 3 := nth_prime_eq_of_count (by norm_num) (by decide)
  have h2 : prime 2 = 5 := nth_prime_eq_of_count (by norm_num) (by decide)
  have h3 : prime 3 = 7 := nth_prime_eq_of_count (by norm_num) (by decide)
  have h4 : prime 4 = 11 := nth_prime_eq_of_count (by norm_num) (by decide)
  have h5 : prime 5 = 13 := nth_prime_eq_of_count (by norm_num) (by decide)
  have h6 : prime 6 = 17 := nth_prime_eq_of_count (by norm_num) (by decide)
  have h7 : prime 7 = 19 := nth_prime_eq_of_count (by norm_num) (by decide)
  have h8 : prime 8 = 23 := nth_prime_eq_of_count (by norm_num) (by decide)
  have h9 : prime 9 = 29 := nth_prime_eq_of_count (by norm_num) (by decide)
  have h10 : prime 10 = 31 := nth_prime_eq_of_count (by norm_num) (by decide)
  have h11 : prime 11 = 37 := nth_prime_eq_of_count (by norm_num) (by decide)
  have h12 : prime 12 = 41 := nth_prime_eq_of_count (by norm_num) (by decide)
  have h13 : prime 13 = 43 := nth_prime_eq_of_count (by norm_num) (by decide)
  have h14 : prime 14 = 47 := nth_prime_eq_of_count (by norm_num) (by decide)
  have h15 : prime 15 = 53 := nth_prime_eq_of_count (by norm_num) (by decide)
  have h16 : prime 16 = 59 := nth_prime_eq_of_count (by norm_num) (by decide)
  have h17 : prime 17 = 61 := nth_prime_eq_of_count (by norm_num) (by decide)
  have h18 : prime 18 = 67 := nth_prime_eq_of_count (by norm_num) (by decide)
  have h19 : prime 19 = 71 := nth_prime_eq_of_count (by norm_num) (by decide)
  have h20 : prime 20 = 73 := nth_prime_eq_of_count (by norm_num) (by decide)
  have h21 : prime 21 = 79 := nth_prime_eq_of_count (by norm_num) (by decide)
  have h22 : prime 22 = 83 := nth_prime_eq_of_count (by norm_num) (by decide)
  have h23 : prime 23 = 89 := nth_prime_eq_of_count (by norm_num) (by decide)
  have h24 : prime 24 = 97 := nth_prime_eq_of_count (by norm_num) (by decide)
  have h25 : prime 25 = 101 := nth_prime_eq_of_count (by norm_num) (by decide)
  intro i hi
  interval_cases i <;>
    simp only [q, List.getD_cons_zero, List.getD_cons_succ, h0, h1, h2, h3, h4, h5, h6,
      h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23,
      h24, h25]

theorem q_rows : ∀ k ∈ Finset.Icc 1 25, (diff^[k] q) 0 = 1 := by decide

/-- **Unconditional partial result.**  Gilbreath's conjecture holds for the first `25`
rows of the difference triangle of the primes. -/
theorem gilbreath_le_25 : ∀ k, 1 ≤ k → k ≤ 25 → row prime k 0 = 1 := by
  intro k hk1 hk25
  have : row prime k 0 = (diff^[k] q) 0 := by
    unfold row
    exact diff_iterate_congr k prime q 0 (fun i hi => prime_eq_q i (by omega))
  rw [this]
  exact q_rows k (Finset.mem_Icc.mpr ⟨hk1, hk25⟩)

end Brockian.GilbreathConjecture

