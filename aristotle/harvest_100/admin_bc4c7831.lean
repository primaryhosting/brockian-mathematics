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

A *Ruth–Aaron pair* is a pair of consecutive positive integers `(n, n+1)` whose sums of prime
factors, counted with multiplicity, agree:  `sopfr n = sopfr (n+1)`.  The first examples are
`(5,6)`, `(8,9)`, `(15,16)`, `(77,78)`, `(125,126)` and the famous `(714,715)`.

Whether there are infinitely many Ruth–Aaron pairs is an open problem (Erdős conjectured that
there are).  Accordingly, this file develops the theory and proves a *conditional reduction*:
Ruth–Aaron infinitude follows from a hypothesis asserting only the primality of two explicit
numbers, with no reference to sums of prime factors of the resulting pair.

The reduction rests on the following exact identity.  Write `Δ c = sopfr (c+1) - sopfr c`, put

  `p = 1 + (c+1) * Δ c`,  `q = 1 + c * Δ c`,  `n = c * p`.

Then, purely algebraically, `n + 1 = (c+1) * q`, and since `sopfr` is completely additive,

  `sopfr n = sopfr c + p`,  `sopfr (n+1) = sopfr (c+1) + q = sopfr c + Δ c + q = sopfr c + p`,

so `(n, n+1)` is a Ruth–Aaron pair *whenever `p` and `q` are both prime*.  Thus the sum-of-prime-
factors condition disappears entirely, and only a two-fold primality condition remains.

For instance `c = 1` gives `Δ = 2`, `q = 3`, `p = 5`, `n = 5`, the pair `(5,6)`; and `c = 12`
gives `Δ = 6`, `q = 73`, `p = 79`, `n = 948 = 2^2·3·79` with `949 = 13·73`, both of
sum-of-prime-factors `86`.
-/

namespace Brockian.RuthAaronPairs

open scoped Nat

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity
(with the convention `sopfr 0 = sopfr 1 = 0`). -/
def sopfr (n : ℕ) : ℕ := (Nat.primeFactorsList n).sum

@[simp] lemma sopfr_zero : sopfr 0 = 0 := by simp [sopfr]

@[simp] lemma sopfr_one : sopfr 1 = 0 := by simp [sopfr]

/-- For a prime `p`, `sopfr p = p`. -/
lemma sopfr_prime {p : ℕ} (hp : Nat.Prime p) : sopfr p = p := by
  simp [sopfr, Nat.primeFactorsList_prime hp]

/-- `sopfr` is completely additive: it turns products into sums. -/
lemma sopfr_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    sopfr (a * b) = sopfr a + sopfr b := by
  have h := Nat.perm_primeFactorsList_mul ha hb
  simpa [sopfr, List.sum_append] using h.sum_eq

/-- `n` is the smaller member of a Ruth–Aaron pair: `n` and `n+1` are positive integers with
the same sum of prime factors (counted with multiplicity). -/
def IsRuthAaronPair (n : ℕ) : Prop := 0 < n ∧ sopfr n = sopfr (n + 1)

/-- The set of Ruth–Aaron pairs, indexed by their smaller member. -/
def ruthAaronSet : Set ℕ := {n | IsRuthAaronPair n}

/-! ### Some concrete Ruth–Aaron pairs -/

private lemma sopfr_two : sopfr 2 = 2 := sopfr_prime (by norm_num)
private lemma sopfr_three : sopfr 3 = 3 := sopfr_prime (by norm_num)
private lemma sopfr_five : sopfr 5 = 5 := sopfr_prime (by norm_num)
private lemma sopfr_seven : sopfr 7 = 7 := sopfr_prime (by norm_num)
private lemma sopfr_eleven : sopfr 11 = 11 := sopfr_prime (by norm_num)
private lemma sopfr_thirteen : sopfr 13 = 13 := sopfr_prime (by norm_num)
private lemma sopfr_seventeen : sopfr 17 = 17 := sopfr_prime (by norm_num)

/-- `(5,6)` is a Ruth–Aaron pair: `5 = 5` and `6 = 2·3`, both with prime-factor sum `5`. -/
theorem isRuthAaronPair_five : IsRuthAaronPair 5 := by
  refine ⟨by norm_num, ?_⟩
  have h6 : (6 : ℕ) = 2 * 3 := by norm_num
  rw [show (5 : ℕ) + 1 = 6 from rfl, h6, sopfr_mul (by norm_num) (by norm_num),
    sopfr_two, sopfr_three, sopfr_five]

/-- `(8,9)` is a Ruth–Aaron pair: `8 = 2^3` and `9 = 3^2`, both with prime-factor sum `6`. -/
theorem isRuthAaronPair_eight : IsRuthAaronPair 8 := by
  refine ⟨by norm_num, ?_⟩
  have h8 : (8 : ℕ) = 2 * (2 * 2) := by norm_num
  have h9 : (8 : ℕ) + 1 = 3 * 3 := by norm_num
  rw [h8, h9, sopfr_mul (by norm_num) (by norm_num), sopfr_mul (by norm_num) (by norm_num),
    sopfr_mul (by norm_num) (by norm_num), sopfr_two, sopfr_three]

/-- `(15,16)` is a Ruth–Aaron pair: `15 = 3·5` and `16 = 2^4`, both with prime-factor sum `8`. -/
theorem isRuthAaronPair_fifteen : IsRuthAaronPair 15 := by
  refine ⟨by norm_num, ?_⟩
  have h15 : (15 : ℕ) = 3 * 5 := by norm_num
  have h16 : (15 : ℕ) + 1 = 2 * (2 * (2 * 2)) := by norm_num
  rw [h15, h16, sopfr_mul (by norm_num) (by norm_num), sopfr_mul (by norm_num) (by norm_num),
    sopfr_mul (by norm_num) (by norm_num), sopfr_mul (by norm_num) (by norm_num),
    sopfr_two, sopfr_three, sopfr_five]

/-- `(714,715)` is a Ruth–Aaron pair (the pair that gave the notion its name):
`714 = 2·3·7·17` and `715 = 5·11·13`, both with prime-factor sum `29`. -/
theorem isRuthAaronPair_714 : IsRuthAaronPair 714 := by
  refine ⟨by norm_num, ?_⟩
  have h714 : (714 : ℕ) = 2 * (3 * (7 * 17)) := by norm_num
  have h715 : (714 : ℕ) + 1 = 5 * (11 * 13) := by norm_num
  rw [h714, h715, sopfr_mul (by norm_num) (by norm_num), sopfr_mul (by norm_num) (by norm_num),
    sopfr_mul (by norm_num) (by norm_num), sopfr_mul (by norm_num) (by norm_num),
    sopfr_mul (by norm_num) (by norm_num), sopfr_two, sopfr_three, sopfr_five, sopfr_seven,
    sopfr_eleven, sopfr_thirteen, sopfr_seventeen]

/-! ### Reformulation of infinitude as unboundedness -/

/-- A set of naturals is infinite exactly when it contains arbitrarily large elements.  This is
the contrapositive reformulation of infinitude used below: instead of exhibiting an infinite
set, it suffices to beat every bound. -/
theorem infinite_iff_exists_gt (S : Set ℕ) : S.Infinite ↔ ∀ N : ℕ, ∃ n ∈ S, N < n := by
  constructor
  · intro h N
    exact h.exists_gt N
  · intro h hfin
    obtain ⟨N, hN⟩ := hfin.bddAbove
    obtain ⟨n, hn, hlt⟩ := h N
    exact absurd (hN hn) (not_le.mpr hlt)

/-- Ruth–Aaron infinitude is equivalent to the existence of arbitrarily large Ruth–Aaron pairs. -/
theorem ruthAaronSet_infinite_iff :
    ruthAaronSet.Infinite ↔ ∀ N : ℕ, ∃ n, IsRuthAaronPair n ∧ N < n := by
  simpa [ruthAaronSet, and_comm] using infinite_iff_exists_gt ruthAaronSet

/-! ### The key construction: a Ruth–Aaron pair from two primes -/

/-- **Construction.**  Let `c ≥ 1` and let `d` be the excess `sopfr (c+1) - sopfr c`.
If `p = 1 + (c+1) * d` and `q = 1 + c * d` are both prime, then `n = c * p` is the smaller
member of a Ruth–Aaron pair (indeed `n + 1 = (c+1) * q`).

This is the heart of the reduction: the condition "`sopfr n = sopfr (n+1)`" is replaced by the
primality of two explicit numbers. -/
theorem isRuthAaronPair_mul_of_prime {c d : ℕ} (hc : 0 < c)
    (hd : sopfr (c + 1) = sopfr c + d)
    (hp : Nat.Prime (1 + (c + 1) * d)) (hq : Nat.Prime (1 + c * d)) :
    IsRuthAaronPair (c * (1 + (c + 1) * d)) := by
  have hcne : c ≠ 0 := hc.ne'
  have hc1ne : c + 1 ≠ 0 := Nat.succ_ne_zero c
  refine ⟨Nat.mul_pos hc hp.pos, ?_⟩
  have key : c * (1 + (c + 1) * d) + 1 = (c + 1) * (1 + c * d) := by ring
  rw [key, sopfr_mul hcne hp.ne_zero, sopfr_mul hc1ne hq.ne_zero, sopfr_prime hp,
    sopfr_prime hq, hd]
  ring

/-- The excess of `sopfr` between consecutive integers. -/
def sopfrExcess (c : ℕ) : ℕ := sopfr (c + 1) - sopfr c

/-- **Hypothesis (P).**  There are arbitrarily large `c` for which both
`1 + (c+1) * sopfrExcess c` and `1 + c * sopfrExcess c` are prime.

This is a pure two-fold primality condition.  It is amply supported numerically: there are
`820` such `c` below `2 · 10^5`, the smallest being `c = 1` (giving the pair `(5,6)`) and
`c = 12` (giving the pair `(948, 949)`). -/
def PrimePairHypothesis : Prop :=
  ∀ N : ℕ, ∃ c, N < c ∧ Nat.Prime (1 + (c + 1) * sopfrExcess c) ∧
    Nat.Prime (1 + c * sopfrExcess c)

/-- Each witness of Hypothesis (P) produces a Ruth–Aaron pair larger than the witness. -/
theorem exists_ruthAaronPair_gt_of_prime_pair {c : ℕ} (hc : 0 < c)
    (hp : Nat.Prime (1 + (c + 1) * sopfrExcess c))
    (hq : Nat.Prime (1 + c * sopfrExcess c)) :
    ∃ n, IsRuthAaronPair n ∧ c ≤ n := by
  set d := sopfrExcess c with hdef
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, Nat.mul_zero] at hq
      exact absurd hq Nat.not_prime_one
    · exact h
  have hd : sopfr (c + 1) = sopfr c + d := by
    have : d = sopfr (c + 1) - sopfr c := hdef
    omega
  refine ⟨c * (1 + (c + 1) * d), isRuthAaronPair_mul_of_prime hc hd hp hq, ?_⟩
  calc c = c * 1 := (Nat.mul_one c).symm
    _ ≤ c * (1 + (c + 1) * d) := Nat.mul_le_mul_left c (by omega)

/-- **Ruth–Aaron Infinitude (conditional).**  Assuming Hypothesis (P) — a statement about the
primality of two explicit numbers, with no reference to sums of prime factors — there are
infinitely many Ruth–Aaron pairs.

Unconditional infinitude of Ruth–Aaron pairs is an open problem; this theorem is a
Lean-checked reduction of it to Hypothesis (P). -/
theorem RuthAaronInfinitude (H : PrimePairHypothesis) :
    {n : ℕ | IsRuthAaronPair n}.Infinite := by
  rw [infinite_iff_exists_gt]
  intro N
  obtain ⟨c, hcN, hp, hq⟩ := H (N + 1)
  have hc : 0 < c := by omega
  obtain ⟨n, hn, hcn⟩ := exists_ruthAaronPair_gt_of_prime_pair hc hp hq
  exact ⟨n, hn, by omega⟩

end Brockian.RuthAaronPairs

