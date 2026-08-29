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
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Classical

namespace Brockian.GoldbachComb

/-- `n` is Goldbach representable if it is a sum of two primes. -/
def Representable (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- The number of Goldbach representations `n = p + (n - p)` with both parts prime.
(Ordered representations: the pairs `(p, q)` and `(q, p)` are counted separately.) -/
def goldbachCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).card

/-- The Goldbach indicator, as a real number. -/
noncomputable def goldbachInd (n : ℕ) : ℝ := if Representable n then 1 else 0

/-- Empirical mean of a real-valued arithmetic function over a finite set. -/
noncomputable def mean (S : Finset ℕ) (f : ℕ → ℝ) : ℝ := (∑ n ∈ S, f n) / S.card

/-- Empirical covariance of two real-valued arithmetic functions over a finite set. -/
noncomputable def cov (S : Finset ℕ) (f g : ℕ → ℝ) : ℝ :=
  mean S (fun n => f n * g n) - mean S f * mean S g

/-- Mean number of Goldbach representations over `S`. -/
noncomputable def goldbachMean (S : Finset ℕ) : ℝ := mean S (fun n => (goldbachCount n : ℝ))

/-- Density of Goldbach-representable elements of `S`. -/
noncomputable def goldbachDensity (S : Finset ℕ) : ℝ := mean S goldbachInd

/-- Covariance of the representation count with the Goldbach indicator over `S`. -/
noncomputable def goldbachCov (S : Finset ℕ) : ℝ :=
  cov S (fun n => (goldbachCount n : ℝ)) goldbachInd

/-- The representation count is positive exactly for representable `n`. -/
lemma goldbachCount_pos_iff (n : ℕ) : 0 < goldbachCount n ↔ Representable n := by
  constructor
  · intro h
    rw [goldbachCount, Finset.card_pos] at h
    obtain ⟨p, hp⟩ := h
    rw [Finset.mem_filter, Finset.mem_range] at hp
    exact ⟨p, n - p, hp.2.1, hp.2.2, by omega⟩
  · rintro ⟨p, q, hp, hq, rfl⟩
    rw [goldbachCount, Finset.card_pos]
    refine ⟨p, ?_⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, hp, ?_⟩
    simpa using hq

/-- Pointwise, multiplying the representation count by the Goldbach indicator changes nothing. -/
lemma count_mul_ind (n : ℕ) :
    (goldbachCount n : ℝ) * goldbachInd n = (goldbachCount n : ℝ) := by
  by_cases h : Representable n
  · simp [goldbachInd, h]
  · have h0 : goldbachCount n = 0 := by
      by_contra hne
      exact h ((goldbachCount_pos_iff n).mp (Nat.pos_of_ne_zero hne))
    simp [goldbachInd, h, h0]

lemma goldbachInd_le_one (n : ℕ) : goldbachInd n ≤ 1 := by
  unfold goldbachInd
  split <;> norm_num

/-- The density equals `1` exactly when every element of a nonempty `S` is representable. -/
lemma goldbachDensity_eq_one_iff {S : Finset ℕ} (hS : S.Nonempty) :
    goldbachDensity S = 1 ↔ ∀ n ∈ S, Representable n := by
  have hc : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hS)
  rw [goldbachDensity, mean, div_eq_one_iff_eq hc]
  constructor
  · intro h n hn
    have hsum : ∑ m ∈ S, (1 - goldbachInd m) = 0 := by
      rw [Finset.sum_sub_distrib, h]
      simp
    have hnonneg : ∀ m ∈ S, 0 ≤ 1 - goldbachInd m := fun m _ => by
      have := goldbachInd_le_one m; linarith
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum n hn
    by_contra hcon
    rw [goldbachInd, if_neg hcon] at hzero
    norm_num at hzero
  · intro h
    rw [Finset.sum_congr rfl (fun n hn => show goldbachInd n = 1 by
      rw [goldbachInd, if_pos (h n hn)])]
    simp

/-- **Goldbach Covariance Transfer.**

For any nonempty finite set `S` of naturals:

1. (Transfer identity) The empirical covariance over `S` between the Goldbach
   representation count `r(n)` and the Goldbach indicator `1_{r(n) > 0}` factors as
   `mean(r) * (1 - density)`; i.e. the covariance carries no information beyond the
   mean count and the density of representable elements of `S`.
2. (Reduction) Consequently, whenever the mean representation count over `S` is positive,
   the covariance vanishes if and only if *every* element of `S` is a sum of two primes.
-/
theorem GoldbachCovarianceTransfer (S : Finset ℕ) (hS : S.Nonempty) :
    goldbachCov S = goldbachMean S * (1 - goldbachDensity S) ∧
      (0 < goldbachMean S → (goldbachCov S = 0 ↔ ∀ n ∈ S, Representable n)) := by
  have key : goldbachCov S = goldbachMean S * (1 - goldbachDensity S) := by
    have h1 : mean S (fun n => (goldbachCount n : ℝ) * goldbachInd n)
        = mean S (fun n => (goldbachCount n : ℝ)) := by
      unfold mean
      rw [Finset.sum_congr rfl (fun n _ => count_mul_ind n)]
    rw [goldbachCov, cov, h1, goldbachMean, goldbachDensity]
    ring
  refine ⟨key, fun hpos => ?_⟩
  rw [key]
  constructor
  · intro h
    have hd : 1 - goldbachDensity S = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' (ne_of_gt hpos)
      · exact h'
    exact (goldbachDensity_eq_one_iff hS).mp (by linarith)
  · intro h
    rw [(goldbachDensity_eq_one_iff hS).mpr h]
    ring

/-- Sanity check (non-vacuity): the positivity hypothesis of the reduction is satisfiable,
e.g. for `S = {4}` (with `4 = 2 + 2`). -/
example : 0 < goldbachMean ({4} : Finset ℕ) := by
  have h : goldbachCount 4 = 1 := by decide
  simp [goldbachMean, mean, h]

end Brockian.GoldbachComb

