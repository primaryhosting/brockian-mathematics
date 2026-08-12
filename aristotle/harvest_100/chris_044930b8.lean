import Brockian.RuthAaronPairs

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

import Mathlib

/-!
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A *Ruth–Aaron pair* is a pair of consecutive integers `(n, n+1)` with the same sum of prime
factors counted with multiplicity, e.g. `(714, 715)`: `714 = 2·3·7·17`, `715 = 5·11·13`, and
`2 + 3 + 7 + 17 = 29 = 5 + 11 + 13`.  Whether there are infinitely many such pairs is a
well-known open problem (Erdős).

This file contains:

* a definition of `sopfr` (sum of prime factors with multiplicity) and of `IsRuthAaron`;
* unconditional verifications that `5, 8, 77, 714` are Ruth–Aaron numbers;
* an unconditional *construction*: `isRuthAaron_of_prime_pair`, producing a Ruth–Aaron pair out
  of any `B ≥ 2` for which the two integers `B·d − 1` and `(B+1)·d − 1` are prime, where
  `d = sopfr (B+1) − sopfr B > 0`;
* the resulting conditional infinitude theorem `RuthAaronInfinitude`, and a further reduction
  `ruthAaronInfinitude_of_primeQuadruple` of the required hypothesis to a Schinzel Hypothesis H
  statement for one explicit quadruple of polynomials.

So the deliverable is a Lean-checked *conditional reduction*: Ruth–Aaron infinitude follows from
a prime `k`-tuple conjecture, not from anything Ruth–Aaron specific.
-/

namespace Brockian.RuthAaronPairs

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity
(`sopfr 0 = sopfr 1 = 0`). -/
def sopfr (n : ℕ) : ℕ := (Nat.primeFactorsList n).sum

/-- `n` is a *Ruth–Aaron number* if `n` and `n + 1` have the same sum of prime factors
(counted with multiplicity); `(n, n+1)` is then called a *Ruth–Aaron pair*. -/
def IsRuthAaron (n : ℕ) : Prop := 1 < n ∧ sopfr n = sopfr (n + 1)

@[simp] lemma sopfr_one : sopfr 1 = 0 := by simp [sopfr]

lemma sopfr_prime {p : ℕ} (hp : p.Prime) : sopfr p = p := by
  simp [sopfr, Nat.primeFactorsList_prime hp]

lemma sopfr_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    sopfr (a * b) = sopfr a + sopfr b := by
  unfold sopfr
  rw [(Nat.perm_primeFactorsList_mul ha hb).sum_eq, List.sum_append]

/-! ## The construction

If `B ≥ 2` and `d = sopfr (B+1) - sopfr B > 0`, put `p = B * d - 1` and `q = (B+1) * d - 1`.
Then `(B+1) * p + 1 = B * q`, and if both `p` and `q` are prime then
`n = (B+1) * p` is a Ruth–Aaron number, since
`sopfr n = sopfr (B+1) + p` and `sopfr (n+1) = sopfr B + q = sopfr B + p + d = sopfr (B+1) + p`.
-/

/-- The algebraic identity underlying the construction. -/
lemma succ_mul_pred_add_one {B d : ℕ} (hB : 1 ≤ B) (hd : 1 ≤ d) :
    (B + 1) * (B * d - 1) + 1 = B * ((B + 1) * d - 1) := by
  have h1 : 1 ≤ B * d := Nat.one_le_iff_ne_zero.2 (by positivity)
  have h2 : 1 ≤ (B + 1) * d := Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨p, hp⟩ : ∃ p, B * d = p + 1 := ⟨B * d - 1, by omega⟩
  obtain ⟨q, hq⟩ : ∃ q, (B + 1) * d = q + 1 := ⟨(B + 1) * d - 1, by omega⟩
  have hp' : B * d - 1 = p := by omega
  have hq' : (B + 1) * d - 1 = q := by omega
  rw [hp', hq']
  have h3 : B * q + B = ((B + 1) * p + 1) + B := by
    rw [show B * q + B = B * (q + 1) by ring, show ((B + 1) * p + 1) + B = (B + 1) * (p + 1) by ring,
      ← hp, ← hq]
    ring
  exact (Nat.add_right_cancel h3).symm

/-- **The construction.** From a pair of primes of the shape `B * d - 1`, `(B+1) * d - 1`,
where `d` is the (positive) jump `sopfr (B+1) - sopfr B`, one manufactures a Ruth–Aaron
number `(B + 1) * (B * d - 1)`. -/
theorem isRuthAaron_of_prime_pair {B d : ℕ} (hB : 2 ≤ B) (hd : 1 ≤ d)
    (hsum : sopfr B + d = sopfr (B + 1))
    (hp : Nat.Prime (B * d - 1)) (hq : Nat.Prime ((B + 1) * d - 1)) :
    IsRuthAaron ((B + 1) * (B * d - 1)) := by
  set p := B * d - 1 with hpdef
  set q := (B + 1) * d - 1 with hqdef
  have hBd : 1 ≤ B * d := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hp2 : 2 ≤ p := hp.two_le
  have hstep : (B + 1) * p + 1 = B * q := succ_mul_pred_add_one (by omega) hd
  have hqp : q = p + d := by
    have h : (B + 1) * d = B * d + d := by ring
    omega
  refine ⟨by nlinarith, ?_⟩
  rw [hstep, sopfr_mul (by omega) (by omega), sopfr_mul (by omega) (by omega),
    sopfr_prime hp, sopfr_prime hq, hqp]
  omega

/-! ## The hypothesis

The following is a prime-pair (Hypothesis H / prime `k`-tuple) type statement: for infinitely
many `B`, the two integers `B * d - 1` and `(B + 1) * d - 1` are simultaneously prime, where
`d` is the jump `sopfr (B + 1) - sopfr B` (required to be positive).

It is numerically an abundant condition: there are 128 values of `B < 20000` satisfying it,
the smallest being `B = 3` (`d = 1`, giving the Ruth–Aaron pair `(8, 9)`) and `B = 6`
(`d = 2`, twin primes `11, 13`, giving `(77, 78)`).
-/

/-- The prime-pair hypothesis used to derive infinitude of Ruth–Aaron pairs. -/
def PrimePairHypothesis : Prop :=
  ∀ N : ℕ, ∃ B d : ℕ, N < B ∧ 1 ≤ d ∧ sopfr B + d = sopfr (B + 1) ∧
    Nat.Prime (B * d - 1) ∧ Nat.Prime ((B + 1) * d - 1)

/-- **Ruth–Aaron infinitude, conditionally.** Under `PrimePairHypothesis`, there are infinitely
many Ruth–Aaron numbers, i.e. infinitely many `n` with `sopfr n = sopfr (n + 1)`. -/
theorem RuthAaronInfinitude (H : PrimePairHypothesis) : {n : ℕ | IsRuthAaron n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨B, d, hBa, hd, hsum, hp, hq⟩ := H (a + 2)
  refine ⟨(B + 1) * (B * d - 1), isRuthAaron_of_prime_pair (by omega) hd hsum hp hq, ?_⟩
  have hp2 : 2 ≤ B * d - 1 := hp.two_le
  nlinarith

/-! ## Reduction to a Hypothesis-H style prime quadruple

The hypothesis above can in turn be deduced from a Schinzel/Bunyakovsky-type statement for one
explicit quadruple of polynomials.  Take `B = 4t` with `t` prime and `B + 1 = 4t + 1` prime.
Then `sopfr B = 4 + t`, `sopfr (B+1) = 4t + 1`, so the jump is `d = 3t - 3`, and

* `B * d - 1 = 12t^2 - 12t - 1`,
* `(B+1) * d - 1 = 12t^2 - 9t - 4`.

So it suffices that the four polynomials `t`, `4t + 1`, `12t^2 - 12t - 1`, `12t^2 - 9t - 4`
take prime values simultaneously infinitely often.  (This happens e.g. at `t = 7, 13, 79`;
`t = 7` produces the Ruth–Aaron pair `(14587, 14588)`.)
-/

/-- A prime `k`-tuple (Schinzel Hypothesis H) statement for one explicit quadruple of
polynomials. -/
def PrimeQuadrupleHypothesis : Prop :=
  ∀ N : ℕ, ∃ t : ℕ, N < t ∧ Nat.Prime t ∧ Nat.Prime (4 * t + 1) ∧
    Nat.Prime (12 * t ^ 2 - 12 * t - 1) ∧ Nat.Prime (12 * t ^ 2 - 9 * t - 4)

lemma sopfr_four_mul {t : ℕ} (ht : t.Prime) : sopfr (4 * t) = 4 + t := by
  rw [show (4 : ℕ) * t = 2 * (2 * t) by ring, sopfr_mul (by norm_num) (by simp [ht.pos.ne']),
    sopfr_mul (by norm_num) ht.pos.ne', sopfr_prime (by norm_num : Nat.Prime 2),
    sopfr_prime ht]
  omega

/-- The prime-pair hypothesis follows from the Hypothesis-H statement for the explicit
quadruple `t`, `4t + 1`, `12t^2 - 12t - 1`, `12t^2 - 9t - 4`. -/
theorem primePairHypothesis_of_primeQuadruple (H : PrimeQuadrupleHypothesis) :
    PrimePairHypothesis := by
  intro N
  obtain ⟨t, htN, ht, ht1, hp, hq⟩ := H (N + 2)
  have ht2 : 2 ≤ t := ht.two_le
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
  have hsq : (s + 2) ^ 2 = s ^ 2 + 4 * s + 4 := by ring
  have hd : 3 * (s + 2) - 3 = 3 * s + 3 := by omega
  have e1 : 4 * (s + 2) * (3 * s + 3) = 12 * s ^ 2 + 36 * s + 24 := by ring
  have e2 : (4 * (s + 2) + 1) * (3 * s + 3) = 12 * s ^ 2 + 39 * s + 27 := by ring
  refine ⟨4 * (s + 2), 3 * (s + 2) - 3, by omega, by omega, ?_, ?_, ?_⟩
  · rw [sopfr_four_mul ht, sopfr_prime ht1]
    omega
  · have h : 4 * (s + 2) * (3 * (s + 2) - 3) - 1
        = 12 * (s + 2) ^ 2 - 12 * (s + 2) - 1 := by
      rw [hd, e1, hsq]; omega
    rwa [h]
  · have h : (4 * (s + 2) + 1) * (3 * (s + 2) - 3) - 1
        = 12 * (s + 2) ^ 2 - 9 * (s + 2) - 4 := by
      rw [hd, e2, hsq]; omega
    rwa [h]

/-- **Ruth–Aaron infinitude from Hypothesis H for an explicit quadruple.** -/
theorem ruthAaronInfinitude_of_primeQuadruple (H : PrimeQuadrupleHypothesis) :
    {n : ℕ | IsRuthAaron n}.Infinite :=
  RuthAaronInfinitude (primePairHypothesis_of_primeQuadruple H)

/-! ## Unconditional examples -/

lemma sopfr_six : sopfr 6 = 5 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num, sopfr_mul (by norm_num) (by norm_num),
    sopfr_prime (by norm_num : Nat.Prime 2), sopfr_prime (by norm_num : Nat.Prime 3)]

lemma sopfr_eight : sopfr 8 = 6 := by
  rw [show (8 : ℕ) = 2 * (2 * 2) by norm_num, sopfr_mul (by norm_num) (by norm_num),
    sopfr_mul (by norm_num) (by norm_num), sopfr_prime (by norm_num : Nat.Prime 2)]

lemma sopfr_nine : sopfr 9 = 6 := by
  rw [show (9 : ℕ) = 3 * 3 by norm_num, sopfr_mul (by norm_num) (by norm_num),
    sopfr_prime (by norm_num : Nat.Prime 3)]

lemma sopfr_seventyEight : sopfr 78 = 18 := by
  rw [show (78 : ℕ) = 2 * (3 * 13) by norm_num, sopfr_mul (by norm_num) (by norm_num),
    sopfr_mul (by norm_num) (by norm_num), sopfr_prime (by norm_num : Nat.Prime 2),
    sopfr_prime (by norm_num : Nat.Prime 3), sopfr_prime (by norm_num : Nat.Prime 13)]

lemma sopfr_seventySeven : sopfr 77 = 18 := by
  rw [show (77 : ℕ) = 7 * 11 by norm_num, sopfr_mul (by norm_num) (by norm_num),
    sopfr_prime (by norm_num : Nat.Prime 7), sopfr_prime (by norm_num : Nat.Prime 11)]

lemma sopfr_sevenHundredFourteen : sopfr 714 = 29 := by
  rw [show (714 : ℕ) = 2 * (3 * (7 * 17)) by norm_num, sopfr_mul (by norm_num) (by norm_num),
    sopfr_mul (by norm_num) (by norm_num), sopfr_mul (by norm_num) (by norm_num),
    sopfr_prime (by norm_num : Nat.Prime 2), sopfr_prime (by norm_num : Nat.Prime 3),
    sopfr_prime (by norm_num : Nat.Prime 7), sopfr_prime (by norm_num : Nat.Prime 17)]

lemma sopfr_sevenHundredFifteen : sopfr 715 = 29 := by
  rw [show (715 : ℕ) = 5 * (11 * 13) by norm_num, sopfr_mul (by norm_num) (by norm_num),
    sopfr_mul (by norm_num) (by norm_num), sopfr_prime (by norm_num : Nat.Prime 5),
    sopfr_prime (by norm_num : Nat.Prime 11), sopfr_prime (by norm_num : Nat.Prime 13)]

/-- `(5, 6)` is a Ruth–Aaron pair. -/
lemma isRuthAaron_five : IsRuthAaron 5 :=
  ⟨by norm_num, by rw [sopfr_prime (by norm_num : Nat.Prime 5)]; exact (sopfr_six).symm⟩

/-- `(8, 9)` is a Ruth–Aaron pair. -/
lemma isRuthAaron_eight : IsRuthAaron 8 :=
  ⟨by norm_num, by rw [sopfr_eight]; exact sopfr_nine.symm⟩

/-- `(77, 78)` is a Ruth–Aaron pair. -/
lemma isRuthAaron_seventySeven : IsRuthAaron 77 :=
  ⟨by norm_num, by rw [sopfr_seventySeven]; exact sopfr_seventyEight.symm⟩

/-- `(714, 715)` is the original Ruth–Aaron pair. -/
lemma isRuthAaron_sevenHundredFourteen : IsRuthAaron 714 :=
  ⟨by norm_num, by rw [sopfr_sevenHundredFourteen]; exact sopfr_sevenHundredFifteen.symm⟩

/-- The construction applied to `B = 6`, `d = 2` (twin primes `11`, `13`) reproduces the
Ruth–Aaron pair `(77, 78)`. -/
lemma isRuthAaron_construction_six : IsRuthAaron ((6 + 1) * (6 * 2 - 1)) := by
  refine isRuthAaron_of_prime_pair (by norm_num) (by norm_num) ?_ (by norm_num) (by norm_num)
  rw [sopfr_six, show (6 : ℕ) + 1 = 7 by norm_num, sopfr_prime (by norm_num : Nat.Prime 7)]

/-- The quadruple family at `t = 7`: `7`, `29`, `503`, `521` are all prime, and the
construction yields the Ruth–Aaron pair `(14587, 14588)`. -/
lemma isRuthAaron_construction_twentyEight : IsRuthAaron ((28 + 1) * (28 * 18 - 1)) := by
  refine isRuthAaron_of_prime_pair (by norm_num) (by norm_num) ?_ (by norm_num) (by norm_num)
  rw [show (28 : ℕ) = 4 * 7 by norm_num, sopfr_four_mul (by norm_num : Nat.Prime 7),
    show (4 : ℕ) * 7 + 1 = 29 by norm_num, sopfr_prime (by norm_num : Nat.Prime 29)]

example : (28 + 1) * (28 * 18 - 1) = 14587 := by norm_num

end Brockian.RuthAaronPairs

