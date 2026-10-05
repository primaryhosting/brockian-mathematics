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

(Lean 4 requires `import` to precede every command, including module docstrings,
so the required header is reproduced verbatim as a module docstring just below
the import as well.)
-/

import Mathlib

/-!
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Brockian
namespace GoldbachComb

/-! ## Averages and covariance over a finite sample -/

/-- The empirical mean of `f` over a finite set `S` of naturals. -/
noncomputable def mean (S : Finset ℕ) (f : ℕ → ℝ) : ℝ := (∑ n ∈ S, f n) / S.card

/-- The empirical covariance of `f` and `g` over a finite set `S` of naturals. -/
noncomputable def cov (S : Finset ℕ) (f g : ℕ → ℝ) : ℝ :=
  mean S (fun n => f n * g n) - mean S f * mean S g

lemma card_ne_zero_of_nonempty {S : Finset ℕ} (hS : S.Nonempty) : ((S.card : ℝ)) ≠ 0 := by
  have : 0 < S.card := Finset.card_pos.mpr hS
  positivity

lemma mean_sub (S : Finset ℕ) (f g : ℕ → ℝ) :
    mean S (fun n => f n - g n) = mean S f - mean S g := by
  simp [mean, Finset.sum_sub_distrib, sub_div]

lemma mean_const {S : Finset ℕ} (hS : S.Nonempty) (c : ℝ) : mean S (fun _ => c) = c := by
  rw [mean, Finset.sum_const, nsmul_eq_mul]
  field_simp [card_ne_zero_of_nonempty hS]

lemma mean_const_one {S : Finset ℕ} (hS : S.Nonempty) : mean S (fun _ => (1 : ℝ)) = 1 :=
  mean_const hS 1

lemma mean_nonneg {S : Finset ℕ} {f : ℕ → ℝ} (hf : ∀ n ∈ S, 0 ≤ f n) : 0 ≤ mean S f := by
  apply div_nonneg (Finset.sum_nonneg hf)
  positivity

/-- If `|h|` is dominated pointwise by `f` on `S`, then `|mean h| ≤ mean f`. -/
lemma abs_mean_le_mean {S : Finset ℕ} {h f : ℕ → ℝ} (hb : ∀ n ∈ S, |h n| ≤ f n) :
    |mean S h| ≤ mean S f := by
  have hsum : |∑ n ∈ S, h n| ≤ ∑ n ∈ S, f n :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hb)
  rw [mean, mean, abs_div, Nat.abs_cast]
  gcongr

lemma mean_mul_const (S : Finset ℕ) (f : ℕ → ℝ) (c : ℝ) :
    mean S (fun n => f n * c) = mean S f * c := by
  simp [mean, ← Finset.sum_mul, div_mul_eq_mul_div]

/-! ## Goldbach representability -/

/-- `n` is *Goldbach representable* if it is a sum of two primes. -/
def IsGoldbach (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- Indicator of Goldbach representability. -/
noncomputable def goldbachIndicator (n : ℕ) : ℝ := if IsGoldbach n then 1 else 0

/-- Indicator of the Goldbach exceptions (numbers that are *not* sums of two primes). -/
noncomputable def exceptionIndicator (n : ℕ) : ℝ := 1 - goldbachIndicator n

lemma exceptionIndicator_nonneg (n : ℕ) : 0 ≤ exceptionIndicator n := by
  unfold exceptionIndicator goldbachIndicator
  split <;> norm_num

lemma exceptionIndicator_eq_zero {n : ℕ} (h : IsGoldbach n) : exceptionIndicator n = 0 := by
  simp [exceptionIndicator, goldbachIndicator, h]

/-! ## The covariance transfer identity and bound -/

/-- Exact transfer identity: the covariance of the Goldbach indicator with any weight `g`
is expressed purely through the exceptional set. -/
lemma cov_goldbach_eq {S : Finset ℕ} (hS : S.Nonempty) (g : ℕ → ℝ) :
    cov S goldbachIndicator g =
      mean S exceptionIndicator * mean S g - mean S (fun n => exceptionIndicator n * g n) := by
  have hχ : goldbachIndicator = fun n => (1 : ℝ) - exceptionIndicator n := by
    funext n; simp [exceptionIndicator]
  have m1 : mean S goldbachIndicator = 1 - mean S exceptionIndicator := by
    rw [hχ, mean_sub, mean_const_one hS]
  have m2 : mean S (fun n => goldbachIndicator n * g n)
      = mean S g - mean S (fun n => exceptionIndicator n * g n) := by
    have hfun : (fun n => goldbachIndicator n * g n)
        = fun n => g n - exceptionIndicator n * g n := by
      funext n; rw [hχ]; ring
    rw [hfun, mean_sub]
  rw [cov, m1, m2]; ring

/--
**Goldbach Covariance Transfer.**

For any finite sample `S` of naturals and any weight `g` bounded by `M` on `S`,
the empirical covariance of the Goldbach indicator with `g` is controlled by the empirical
density of Goldbach exceptions in `S`:
`|cov S goldbachIndicator g| ≤ 2 * (density of exceptions) * M`.

In particular, if the Goldbach conjecture holds on `S`, the covariance vanishes identically
(see `cov_goldbach_eq_zero`).
-/
theorem GoldbachCovarianceTransfer {S : Finset ℕ} (hS : S.Nonempty) (g : ℕ → ℝ) (M : ℝ)
    (hg : ∀ n ∈ S, |g n| ≤ M) :
    |cov S goldbachIndicator g| ≤ 2 * mean S exceptionIndicator * M := by
  have he : 0 ≤ mean S exceptionIndicator :=
    mean_nonneg fun n _ => exceptionIndicator_nonneg n
  have hgm : |mean S g| ≤ M := by
    have := abs_mean_le_mean (S := S) (h := g) (f := fun _ => M) hg
    rwa [mean_const hS] at this
  have h1 : |mean S exceptionIndicator * mean S g| ≤ mean S exceptionIndicator * M := by
    rw [abs_mul, abs_of_nonneg he]
    exact mul_le_mul_of_nonneg_left hgm he
  have h2 : |mean S (fun n => exceptionIndicator n * g n)| ≤ mean S exceptionIndicator * M := by
    have hb : ∀ n ∈ S, |exceptionIndicator n * g n| ≤ exceptionIndicator n * M := by
      intro n hn
      rw [abs_mul, abs_of_nonneg (exceptionIndicator_nonneg n)]
      exact mul_le_mul_of_nonneg_left (hg n hn) (exceptionIndicator_nonneg n)
    have := abs_mean_le_mean (S := S) (h := fun n => exceptionIndicator n * g n)
      (f := fun n => exceptionIndicator n * M) hb
    rwa [mean_mul_const] at this
  rw [cov_goldbach_eq hS]
  calc |mean S exceptionIndicator * mean S g - mean S (fun n => exceptionIndicator n * g n)|
      ≤ |mean S exceptionIndicator * mean S g|
        + |mean S (fun n => exceptionIndicator n * g n)| := abs_sub _ _
    _ ≤ 2 * mean S exceptionIndicator * M := by linarith

/-- Conditional corollary: if every element of the sample is a sum of two primes, the
Goldbach indicator is uncorrelated with every weight. -/
theorem cov_goldbach_eq_zero {S : Finset ℕ} (hS : S.Nonempty) (g : ℕ → ℝ)
    (hgold : ∀ n ∈ S, IsGoldbach n) : cov S goldbachIndicator g = 0 := by
  have hz : ∀ n ∈ S, exceptionIndicator n = 0 := fun n hn => exceptionIndicator_eq_zero (hgold n hn)
  have m1 : mean S exceptionIndicator = 0 := by
    rw [mean, Finset.sum_congr rfl hz]; simp
  have m2 : mean S (fun n => exceptionIndicator n * g n) = 0 := by
    rw [mean, Finset.sum_congr rfl (fun n hn => by rw [hz n hn, zero_mul])]; simp
  rw [cov_goldbach_eq hS, m1, m2]; ring

end GoldbachComb
end Brockian

