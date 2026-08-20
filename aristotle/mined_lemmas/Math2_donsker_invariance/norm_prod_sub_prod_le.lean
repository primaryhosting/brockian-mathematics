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

lemma norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (f g : ι → ℂ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  revert hf hg
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      intro hf hg
      have hf' : ∀ i ∈ s, ‖f i‖ ≤ 1 := fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
      have hg' : ∀ i ∈ s, ‖g i‖ ≤ 1 := fun i hi ↦ hg i (Finset.mem_insert_of_mem hi)
      have hprodf : ‖∏ i ∈ s, f i‖ ≤ 1 := by
        rw [norm_prod]
        exact Finset.prod_le_one (fun i _ ↦ norm_nonneg _) hf'
      have hga : ‖g a‖ ≤ 1 := hg a (Finset.mem_insert_self a s)
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
      have hsplit : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i
          = (f a - g a) * (∏ i ∈ s, f i) + g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) := by ring
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have h1 : ‖f a - g a‖ * ‖∏ i ∈ s, f i‖ ≤ ‖f a - g a‖ * 1 :=
        mul_le_mul_of_nonneg_left hprodf (norm_nonneg _)
      have h2 : ‖g a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ 1 * ∑ i ∈ s, ‖f i - g i‖ :=
        mul_le_mul hga (ih hf' hg') (norm_nonneg _) zero_le_one
      rw [mul_one] at h1
      rw [one_mul] at h2
      linarith

/-- Third order Taylor estimate for `exp (i r)`, valid for `|r| ≤ 2`. -/
