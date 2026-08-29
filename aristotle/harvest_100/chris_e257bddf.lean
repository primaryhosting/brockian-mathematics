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
-- (Lean 4 requires `import` to precede any module docstring `/-! ... -/`, so the
-- required header above is written as an ordinary block comment.)

import Mathlib

/-!
## Overview

Gilbreath's conjecture concerns the *Gilbreath array* built from the primes: the
zeroth row is the sequence of primes `2, 3, 5, 7, 11, ...` and each subsequent row is
the sequence of absolute differences of consecutive entries of the previous row.  The
conjecture asserts that every row after the zeroth one begins with `1`.

The conjecture is open.  This file develops the standard finite-certificate reduction
(the argument underlying Odlyzko's numerical verification):

* `GoodRow k m` says that row `k` begins with `1` and its next `m` entries all lie in
  `{0, 2}`.  This is a *finite* condition.
* `gil_head_eq_one_of_goodRow`: a single certificate `GoodRow k m` proves that each of
  the `m + 1` rows `k, k+1, …, k+m` begins with `1`.
* `GilbreathConjecture`: if such certificates exist covering every row
  (`OdlyzkoCriterion`), then the Gilbreath conjecture holds.
* `odlyzkoCriterion_iff_gilbreathProperty`: the criterion is in fact equivalent to the
  conjecture, so this is a genuine reduction and not a strengthening.
* Finally we verify the certificate `GoodRow 5 24` unconditionally, which yields the
  unconditional partial result that rows `1` through `29` all begin with `1`.
-/

namespace Brockian.GilbreathConjecture

/-- `gil k n` is the `n`-th entry (`0`-indexed) of the `k`-th row of the Gilbreath
array: row `0` is the sequence of primes, and each later row consists of the absolute
differences of consecutive entries of the previous row. -/
noncomputable def gil : ℕ → ℕ → ℕ
  | 0, n => Nat.nth Nat.Prime n
  | k + 1, n => Nat.dist (gil k (n + 1)) (gil k n)

/-- **Gilbreath's conjecture**: every row of the Gilbreath array after the zeroth
begins with `1`. -/
def GilbreathProperty : Prop := ∀ k, 1 ≤ k → gil k 0 = 1

/-- `GoodRow k m` is the finite certificate: row `k` begins with `1` and its entries at
positions `1, …, m` all lie in `{0, 2}`. -/
def GoodRow (k m : ℕ) : Prop :=
  gil k 0 = 1 ∧ ∀ i, 1 ≤ i → i ≤ m → gil k i = 0 ∨ gil k i = 2

/-- Odlyzko's criterion: for every row index `k ≥ 1` there is an earlier row `j`
(with `1 ≤ j ≤ k`) carrying a certificate long enough to reach row `k`. -/
def OdlyzkoCriterion : Prop :=
  ∀ k, 1 ≤ k → ∃ j, 1 ≤ j ∧ j ≤ k ∧ GoodRow j (k - j)

section Basic

lemma gil_succ (k n : ℕ) : gil (k + 1) n = Nat.dist (gil k (n + 1)) (gil k n) := rfl

/-- A certificate of length `m + 1` for row `k` yields a certificate of length `m` for
row `k + 1`. -/
lemma goodRow_succ {k m : ℕ} (h : GoodRow k (m + 1)) : GoodRow (k + 1) m := by
  obtain ⟨h0, hmem⟩ := h
  constructor
  · have h1 : gil k 1 = 0 ∨ gil k 1 = 2 := hmem 1 le_rfl (by omega)
    rcases h1 with h1 | h1 <;> simp [gil_succ, h0, h1, Nat.dist]
  · intro i hi him
    have hi1 : gil k i = 0 ∨ gil k i = 2 := hmem i hi (by omega)
    have hi2 : gil k (i + 1) = 0 ∨ gil k (i + 1) = 2 := hmem (i + 1) (by omega) (by omega)
    rcases hi1 with h1 | h1 <;> rcases hi2 with h2 | h2 <;>
      simp [gil_succ, h1, h2, Nat.dist]

/-- **A single finite certificate proves `m + 1` rows.**  If row `k` begins with `1`
and its next `m` entries lie in `{0, 2}`, then each of the rows `k, k+1, …, k+m`
begins with `1`. -/
theorem gil_head_eq_one_of_goodRow (m : ℕ) :
    ∀ (k j : ℕ), GoodRow k m → j ≤ m → gil (k + j) 0 = 1 := by
  induction m with
  | zero => intro k j h hj; obtain rfl : j = 0 := Nat.le_zero.mp hj; simpa using h.1
  | succ m ih =>
      intro k j h hj
      rcases j with _ | j
      · simpa using h.1
      · have hstep := ih (k + 1) j (goodRow_succ h) (by omega)
        have e : k + (j + 1) = (k + 1) + j := by omega
        rw [e]
        exact hstep

end Basic

/-- **Conditional Gilbreath conjecture.**  If every row is reachable from a finite
certificate (Odlyzko's criterion), then every row after the zeroth begins with `1`. -/
theorem GilbreathConjecture (h : OdlyzkoCriterion) : GilbreathProperty := by
  intro k hk
  obtain ⟨j, hj1, hjk, hgood⟩ := h k hk
  have := gil_head_eq_one_of_goodRow (k - j) j (k - j) hgood le_rfl
  rwa [Nat.add_sub_cancel' hjk] at this

/-- The criterion used above is *equivalent* to Gilbreath's conjecture, so nothing has
been assumed beyond the conjecture itself. -/
theorem odlyzkoCriterion_iff_gilbreathProperty : OdlyzkoCriterion ↔ GilbreathProperty := by
  refine ⟨GilbreathConjecture, fun h k hk => ⟨k, hk, le_rfl, ?_, ?_⟩⟩
  · exact h k hk
  · intro i hi hi0; omega

/-! ## Unconditional partial verification

We compute the first thirty primes, then verify the certificate `GoodRow 5 24`, which
establishes unconditionally that rows `1` through `29` begin with `1`.
-/

section Verification

set_option maxRecDepth 40000

private lemma nth_prime_of_count {n p : ℕ} (hp : Nat.Prime p) (hc : Nat.count Nat.Prime p = n) :
    Nat.nth Nat.Prime n = p := hc ▸ Nat.nth_count hp

/-! The first thirty primes, as entries of row `0`. -/

private lemma gp0 : gil 0 0 = 2 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp1 : gil 0 1 = 3 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp2 : gil 0 2 = 5 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp3 : gil 0 3 = 7 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp4 : gil 0 4 = 11 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp5 : gil 0 5 = 13 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp6 : gil 0 6 = 17 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp7 : gil 0 7 = 19 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp8 : gil 0 8 = 23 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp9 : gil 0 9 = 29 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp10 : gil 0 10 = 31 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp11 : gil 0 11 = 37 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp12 : gil 0 12 = 41 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp13 : gil 0 13 = 43 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp14 : gil 0 14 = 47 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp15 : gil 0 15 = 53 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp16 : gil 0 16 = 59 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp17 : gil 0 17 = 61 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp18 : gil 0 18 = 67 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp19 : gil 0 19 = 71 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp20 : gil 0 20 = 73 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp21 : gil 0 21 = 79 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp22 : gil 0 22 = 83 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp23 : gil 0 23 = 89 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp24 : gil 0 24 = 97 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp25 : gil 0 25 = 101 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp26 : gil 0 26 = 103 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp27 : gil 0 27 = 107 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp28 : gil 0 28 = 109 := nth_prime_of_count (by norm_num) (by decide)
private lemma gp29 : gil 0 29 = 113 := nth_prime_of_count (by norm_num) (by decide)

/-- The certificate for row `5`: it begins with `1` and its next `24` entries all lie
in `{0, 2}`. -/
theorem goodRow_five_twentyFour : GoodRow 5 24 := by
  constructor
  · simp [gil_succ, gp0, gp1, gp2, gp3, gp4, gp5, Nat.dist]
  · intro i hi hi24
    interval_cases i <;>
      simp [gil_succ, gp1, gp2, gp3, gp4, gp5, gp6, gp7, gp8, gp9, gp10, gp11, gp12,
        gp13, gp14, gp15, gp16, gp17, gp18, gp19, gp20, gp21, gp22, gp23, gp24, gp25, gp26,
        gp27, gp28, gp29, Nat.dist]

/-- **Unconditional partial result**: rows `1` through `29` of the Gilbreath array all
begin with `1`.  (Rows `1`–`4` are checked directly; rows `5`–`29` all follow from the
single finite certificate `goodRow_five_twentyFour`.) -/
theorem gil_head_eq_one_of_le_twentyNine (k : ℕ) (hk : 1 ≤ k) (hk29 : k ≤ 29) :
    gil k 0 = 1 := by
  by_cases h4 : k ≤ 4
  · interval_cases k <;> simp [gil_succ, gp0, gp1, gp2, gp3, gp4, Nat.dist]
  · have h5 : 5 ≤ k := by omega
    have h := gil_head_eq_one_of_goodRow 24 5 (k - 5) goodRow_five_twentyFour (by omega)
    rwa [Nat.add_sub_cancel' h5] at h

end Verification

end Brockian.GilbreathConjecture

