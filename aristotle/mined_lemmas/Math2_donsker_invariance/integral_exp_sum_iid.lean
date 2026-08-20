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

lemma integral_exp_sum_iid (μ : Measure ℝ) [IsProbabilityMeasure μ] (N : ℕ) (a : ℕ → ℝ) :
    ∫ ω, Complex.exp (((∑ i ∈ Finset.range N, a i * ω i : ℝ) : ℂ) * Complex.I) ∂(iidLaw μ)
      = ∏ i ∈ Finset.range N, charFun μ (a i) := by
  have hindep : iIndepFun (fun (i : Fin N) (ω : ℕ → ℝ) ↦ ω i) (iidLaw μ) := by
    have := iIndepFun_infinitePi (P := fun _ : ℕ ↦ μ) (X := fun _ : ℕ ↦ (id : ℝ → ℝ))
      (fun _ ↦ measurable_id)
    exact this.precomp (g := (Fin.val : Fin N → ℕ)) Fin.val_injective
  have hmap : ∀ i : ℕ, (iidLaw μ).map (fun ω : ℕ → ℝ ↦ ω i) = μ :=
    fun i ↦ Measure.infinitePi_map_eval _ i
  have h1 : ∀ ω : ℕ → ℝ, Complex.exp (((∑ i ∈ Finset.range N, a i * ω i : ℝ) : ℂ) * Complex.I)
      = ∏ i : Fin N, Complex.exp ((ω i : ℂ) * (a i : ℂ) * Complex.I) := by
    intro ω
    rw [← Complex.exp_sum, ← Fin.sum_univ_eq_sum_range (fun i ↦ a i * ω i) N]
    push_cast
    rw [Finset.sum_mul]
    exact congrArg _ (Finset.sum_congr rfl fun i _ ↦ by ring)
  simp_rw [h1]
  rw [hindep.integral_fun_prod_comp
    (f := fun (i : Fin N) (x : ℝ) ↦ Complex.exp ((x : ℂ) * (a i : ℂ) * Complex.I))
    (fun i ↦ (measurable_pi_apply _).aemeasurable)
    (fun i ↦ (by fun_prop :
      Continuous fun x : ℝ ↦ Complex.exp ((x : ℂ) * (a i : ℂ) * Complex.I)).aestronglyMeasurable)]
  rw [← Fin.prod_univ_eq_prod_range (fun i ↦ charFun μ (a i)) N]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [← integral_map (φ := fun ω : ℕ → ℝ ↦ ω (i : ℕ)) (measurable_pi_apply _).aemeasurable
    (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ ↦ Complex.exp ((x : ℂ) * (a i : ℂ) * Complex.I)) _), hmap,
    charFun_apply_real]
  exact congrArg _ (funext fun y ↦ by ring_nf)

/-- The scalar product of the rescaled walk vector with `s`, written as a linear combination of
the steps. -/
