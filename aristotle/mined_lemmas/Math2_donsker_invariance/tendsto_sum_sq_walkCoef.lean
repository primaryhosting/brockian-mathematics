/-
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import RequestProject.Donsker.Defs
import RequestProject.Donsker.CharFun
import RequestProject.Donsker.CLT
import RequestProject.Donsker.Tight
import RequestProject.Donsker.Levy

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

open MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace

namespace Math2

/-- **Donsker's invariance principle** (convergence of the finite-dimensional distributions).

Let `μ` be the law of a centered step with unit variance, let `S_m` be the associated random walk
with i.i.d. steps (the steps being the coordinates of `ℕ → ℝ` under the product measure
`Math2.iidLaw μ`), and let `W_n(u) = S_{⌊n u⌋} / √n` be the rescaled walk.

Then, for any finite set of times `t 0 ≤ t 1 ≤ … ≤ t (k-1)`, the law `Math2.walkLaw μ t k n` of
the random vector `(W_n(t 0), …, W_n(t (k-1)))` converges weakly, as `n → ∞`, to the law
`Math2.bmLaw t k` of `(B_{t 0}, …, B_{t (k-1)})`, where `B` is a Brownian motion.  Weak
convergence is expressed as convergence of the integrals of all bounded continuous functions.

The limit does not depend on the step distribution `μ` (only on its mean and variance): this is
the invariance in Donsker's invariance principle.  That `Math2.bmLaw t k` really is the
finite-dimensional distribution of Brownian motion is the content of
`Math2.charFun_bmLaw_eq`: it is the centered Gaussian law with covariance
`min (t i) (t j)`. -/

lemma tendsto_sum_sq_walkCoef (ht : Monotone t) (ht0 : 0 ≤ t 0)
    (s : EuclideanSpace ℝ (Fin k)) :
    Tendsto (fun n ↦ ∑ i ∈ Finset.range (stepCount t n k), walkCoef t k n s i ^ 2) atTop
      (𝓝 (∑ l ∈ Finset.range k, bmCoef t k s l ^ 2)) := by
  have hnonneg : ∀ j : ℕ, 0 ≤ t j := fun j ↦ ht0.trans (ht (Nat.zero_le j))
  have hle : ∀ (n : ℕ) (j : Fin k), stepCount t n j ≤ stepCount t n k := by
    intro n j
    apply Nat.floor_le_floor
    have h1 : t j ≤ t k := ht (le_of_lt j.isLt)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  -- rewrite the sum of squares as a quadratic form in the step counts
  have hrewrite : ∀ n : ℕ, ∑ i ∈ Finset.range (stepCount t n k), walkCoef t k n s i ^ 2
      = ∑ j : Fin k, ∑ j' : Fin k,
          ((min (stepCount t n j) (stepCount t n j') : ℕ) : ℝ) / n * (s j * s j') := by
    intro n
    have hsq : ∀ i, walkCoef t k n s i ^ 2
        = (∑ j : Fin k, if i < stepCount t n j then s j else 0) ^ 2 / n := by
      intro i
      rw [walkCoef, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    simp only [hsq]
    rw [← Finset.sum_div]
    have hexp : ∀ i, (∑ j : Fin k, if i < stepCount t n j then s j else 0) ^ 2
        = ∑ j : Fin k, ∑ j' : Fin k,
            ((if i < stepCount t n j then (1 : ℝ) else 0)
              * (if i < stepCount t n j' then (1 : ℝ) else 0)) * (s j * s j') := by
      intro i
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun j' _ ↦ ?_
      split_ifs <;> ring
    simp only [hexp]
    rw [Finset.sum_comm]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl fun j' _ ↦ ?_
    have hcard : ∑ i ∈ Finset.range (stepCount t n k),
        ((if i < stepCount t n j then (1 : ℝ) else 0)
          * (if i < stepCount t n j' then (1 : ℝ) else 0)) * (s j * s j')
        = ((min (stepCount t n j) (stepCount t n j') : ℕ) : ℝ) * (s j * s j') := by
      rw [← Finset.sum_mul]
      congr 1
      have : ∀ i, ((if i < stepCount t n j then (1 : ℝ) else 0)
          * (if i < stepCount t n j' then (1 : ℝ) else 0))
          = if i < min (stepCount t n j) (stepCount t n j') then (1 : ℝ) else 0 := by
        intro i
        by_cases h1 : i < stepCount t n j <;> by_cases h2 : i < stepCount t n j' <;>
          simp [h1, h2]
      simp only [this]
      exact sum_range_indicator_lt ((min_le_left _ _).trans (hle n j))
    rw [hcard]
    ring
  simp only [hrewrite]
  -- pass to the limit in each term
  have hterm : ∀ j j' : Fin k,
      Tendsto (fun n : ℕ ↦ ((min (stepCount t n j) (stepCount t n j') : ℕ) : ℝ) / n
        * (s j * s j')) atTop (𝓝 (min (t j) (t j') * (s j * s j'))) := by
    intro j j'
    have h1 := tendsto_stepCount_div (t j) (hnonneg j)
    have h2 := tendsto_stepCount_div (t j') (hnonneg j')
    have hmin : ∀ n : ℕ, ((min (stepCount t n j) (stepCount t n j') : ℕ) : ℝ) / n
        = min ((⌊(n : ℝ) * t j⌋₊ : ℝ) / n) ((⌊(n : ℝ) * t j'⌋₊ : ℝ) / n) := by
      intro n
      rw [stepCount, stepCount, Nat.cast_min,
        min_div_div_right (by positivity : (0 : ℝ) ≤ (n : ℝ))]
    simp only [hmin]
    exact (h1.min h2).mul_const _
  have hsum := tendsto_finset_sum (Finset.univ : Finset (Fin k))
    (fun j _ ↦ tendsto_finset_sum (Finset.univ : Finset (Fin k)) fun j' _ ↦ hterm j j')
  have heq : (∑ i : Fin k, ∑ j : Fin k, min (t i) (t j) * s i * s j)
      = ∑ j : Fin k, ∑ j' : Fin k, min (t j) (t j') * (s j * s j') :=
    Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun j' _ ↦ by ring
  rw [sum_sq_bmCoef k t ht ht0 s, heq]
  exact hsum

/-- **Central limit estimate**: the characteristic functions of the rescaled random walk converge
pointwise to the characteristic function of the finite-dimensional distribution of Brownian
motion. -/
