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

lemma inner_bmVec (k : ℕ) (t : ℕ → ℝ) (z : ℕ → ℝ) (s : EuclideanSpace ℝ (Fin k)) :
    ⟪bmVec t k z, s⟫ = ∑ l ∈ Finset.range k, bmCoef t k s l * z l := by
  have hcoord : ∀ j : Fin k, (bmVec t k z) j
      = ∑ l ∈ Finset.range ((j : ℕ) + 1), Real.sqrt (incr t l) * z l := fun j ↦ rfl
  have key : ∀ j : Fin k, ∑ l ∈ Finset.range ((j : ℕ) + 1), Real.sqrt (incr t l) * z l
      = ∑ l ∈ Finset.range k, (if l ≤ (j : ℕ) then Real.sqrt (incr t l) * z l else 0) := by
    intro j
    rw [← Finset.sum_filter]
    congr 1
    ext l
    simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
    exact ⟨fun h ↦ ⟨lt_of_le_of_lt h j.isLt, h⟩, fun h ↦ h.2⟩
  rw [PiLp.inner_apply]
  simp only [hcoord, RCLike.inner_apply, conj_trivial, bmCoef, key,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> ring

/-- The characteristic function of the law of the rescaled walk. -/
