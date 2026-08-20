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
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.GoldbachComb

open Finset

/-- `goldbachCount n` is the number of ordered Goldbach representations of `n`, i.e. the
number of primes `p ≤ n` such that `n - p` is also prime. -/
def goldbachCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).card

/-- `10 = 3 + 7 = 5 + 5 = 7 + 3`, so `goldbachCount 10 = 3`. -/
theorem goldbachCount_ten : goldbachCount 10 = 3 := by decide

/-- The empirical mean of `f` over a finite index set `S`. (For `S = ∅` this is `0`.) -/
noncomputable def mean (S : Finset ℕ) (f : ℕ → ℝ) : ℝ := (∑ n ∈ S, f n) / S.card

/-- The empirical covariance of `f` and `g` over a finite index set `S`. -/
noncomputable def cov (S : Finset ℕ) (f g : ℕ → ℝ) : ℝ :=
  mean S (fun n => f n * g n) - mean S f * mean S g

theorem mean_empty (f : ℕ → ℝ) : mean ∅ f = 0 := by
  simp [mean]

theorem cov_empty (f g : ℕ → ℝ) : cov ∅ f g = 0 := by
  simp [cov, mean_empty]

theorem cov_comm (S : Finset ℕ) (f g : ℕ → ℝ) : cov S f g = cov S g f := by
  simp only [cov, mean, mul_comm]

/-- **Affine covariance transfer.** Empirical covariance is bilinear up to translations:
rescaling the two observables by `a` and `b` and translating them by constants `c` and `d`
multiplies the covariance by `a * b`. -/
theorem cov_affine (S : Finset ℕ) (f g : ℕ → ℝ) (a b c d : ℝ) :
    cov S (fun n => a * f n + c) (fun n => b * g n + d) = a * b * cov S f g := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp [cov_empty]
  · have hN : (S.card : ℝ) ≠ 0 := by
      have : 0 < S.card := Finset.card_pos.mpr hS
      positivity
    have h1 : ∑ n ∈ S, ((a * f n + c) * (b * g n + d))
        = a * b * (∑ n ∈ S, f n * g n) + a * d * (∑ n ∈ S, f n)
          + c * b * (∑ n ∈ S, g n) + c * d * S.card := by
      rw [Finset.sum_congr rfl (fun n _ => by ring :
        ∀ n ∈ S, (a * f n + c) * (b * g n + d)
          = a * b * (f n * g n) + a * d * f n + c * b * g n + c * d)]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring
    have h2 : ∑ n ∈ S, (a * f n + c) = a * (∑ n ∈ S, f n) + c * S.card := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring
    have h3 : ∑ n ∈ S, (b * g n + d) = b * (∑ n ∈ S, g n) + d * S.card := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring
    simp only [cov, mean, h1, h2, h3]
    field_simp
    ring

/-- **Goldbach Covariance Transfer.**
For any finite family `S` of integers, any lag `k`, and any affine renormalisation
`r ↦ a * r + c`, `r ↦ b * r + d` of the Goldbach representation counts, the empirical
covariance of the renormalised counts of `n` and of `n + k` equals `a * b` times the
covariance of the raw counts. In particular, the vanishing (and, for `a * b > 0`, the sign)
of the Goldbach count covariance is invariant under affine renormalisation. -/
theorem GoldbachCovarianceTransfer (S : Finset ℕ) (k : ℕ) (a b c d : ℝ) :
    cov S (fun n => a * (goldbachCount n : ℝ) + c)
          (fun n => b * (goldbachCount (n + k) : ℝ) + d)
      = a * b * cov S (fun n => (goldbachCount n : ℝ))
                      (fun n => (goldbachCount (n + k) : ℝ)) :=
  cov_affine S _ _ a b c d

end Brockian.GoldbachComb

