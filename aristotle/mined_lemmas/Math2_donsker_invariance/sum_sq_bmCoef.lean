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

lemma sum_sq_bmCoef (k : ℕ) (t : ℕ → ℝ) (ht : Monotone t) (ht0 : 0 ≤ t 0)
    (s : EuclideanSpace ℝ (Fin k)) :
    ∑ l ∈ Finset.range k, (bmCoef t k s l) ^ 2
      = ∑ i : Fin k, ∑ j : Fin k, min (t i) (t j) * s i * s j := by
  have hsq : ∀ l, (bmCoef t k s l) ^ 2
      = incr t l * ∑ i : Fin k, ∑ j : Fin k,
          (if l ≤ (i : ℕ) then (1 : ℝ) else 0) * (if l ≤ (j : ℕ) then (1 : ℝ) else 0)
            * (s i * s j) := by
    intro l
    rw [bmCoef, mul_pow, Real.sq_sqrt (incr_nonneg ht ht0 l)]
    congr 1
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs <;> ring
  simp only [hsq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hfac : ∑ l ∈ Finset.range k, incr t l *
      ((if l ≤ (i : ℕ) then (1 : ℝ) else 0) * (if l ≤ (j : ℕ) then (1 : ℝ) else 0) * (s i * s j))
      = (∑ l ∈ Finset.range k, (if l ≤ min (i : ℕ) (j : ℕ) then incr t l else 0))
        * (s i * s j) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    by_cases h1 : l ≤ (i : ℕ) <;> by_cases h2 : l ≤ (j : ℕ) <;>
      simp [h1, h2]
  have hres : ∑ l ∈ Finset.range k, (if l ≤ min (i : ℕ) (j : ℕ) then incr t l else 0)
      = ∑ l ∈ Finset.range (min (i : ℕ) (j : ℕ) + 1), incr t l := by
    rw [← Finset.sum_filter]
    congr 1
    ext l
    simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨lt_of_le_of_lt (h.trans (min_le_left _ _)) i.isLt, h⟩⟩
  rw [hfac, hres, sum_incr]
  have : t (min (i : ℕ) (j : ℕ)) = min (t i) (t j) := by
    rcases le_total (i : ℕ) (j : ℕ) with h | h
    · rw [min_eq_left h, min_eq_left (ht h)]
    · rw [min_eq_right h, min_eq_right (ht h)]
  rw [this, mul_assoc]

/-- `Math2.bmLaw` is the centered Gaussian law with covariance `min (t i) (t j)`: it is indeed
the finite-dimensional distribution of Brownian motion at the times `t 0, …, t (k-1)`. -/
