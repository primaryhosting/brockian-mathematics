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

lemma inner_walkVec (ht : Monotone t) (n : ℕ) (ω : ℕ → ℝ) (s : EuclideanSpace ℝ (Fin k)) :
    ⟪walkVec t k n ω, s⟫ = ∑ i ∈ Finset.range (stepCount t n k), walkCoef t k n s i * ω i := by
  have hle : ∀ j : Fin k, stepCount t n j ≤ stepCount t n k := by
    intro j
    apply Nat.floor_le_floor
    have : t j ≤ t k := ht (le_of_lt j.isLt)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hcoord : ∀ j : Fin k, (walkVec t k n ω) j
      = (∑ i ∈ Finset.range (stepCount t n j), ω i) / Real.sqrt n := fun j ↦ rfl
  have key : ∀ j : Fin k, ∑ i ∈ Finset.range (stepCount t n j), ω i
      = ∑ i ∈ Finset.range (stepCount t n k), (if i < stepCount t n j then ω i else 0) := by
    intro j
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h ↦ ⟨lt_of_lt_of_le h (hle j), h⟩, fun h ↦ h.2⟩
  rw [PiLp.inner_apply]
  simp only [hcoord, RCLike.inner_apply, conj_trivial, walkCoef, key,
    mul_div_assoc', Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> ring

/-- The scalar product of the Brownian vector with `s`, written as a linear combination of the
increments. -/
