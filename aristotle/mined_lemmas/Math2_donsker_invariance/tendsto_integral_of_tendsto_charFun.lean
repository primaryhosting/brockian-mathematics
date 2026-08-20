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

theorem tendsto_integral_of_tendsto_charFun
    (μ : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (htight : IsTightMeasureSet {μ n | n : ℕ})
    (hchar : ∀ s, Tendsto (fun n ↦ charFun (μ n) s) atTop (𝓝 (charFun ν s)))
    (f : E →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ x, f x ∂(μ n)) atTop (𝓝 (∫ x, f x ∂ν)) := by
  set P : ℕ → ProbabilityMeasure E := fun n ↦ ⟨μ n, inferInstance⟩ with hP
  set Q : ProbabilityMeasure E := ⟨ν, inferInstance⟩ with hQ
  have h := tendsto_probabilityMeasure_of_tendsto_charFun P Q htight hchar
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h f

end Math2

import Mathlib

/-!
# Donsker's invariance principle: basic definitions

We set up the objects appearing in Donsker's theorem:

* `Math2.iidLaw μ`: the law on `ℕ → ℝ` of an i.i.d. sequence with step distribution `μ`;
* `Math2.walkVec t k n ω`: the vector `(S_{⌊n t_0⌋}/√n, …, S_{⌊n t_{k-1}⌋}/√n)` of values of the
  rescaled random walk at the times `t 0, …, t (k-1)`;
* `Math2.bmVec t k z`: the vector `(B_{t_0}, …, B_{t_{k-1}})` of values of a Brownian motion
  built from the i.i.d. standard Gaussian increments `z`;
* `Math2.walkLaw μ t k n` and `Math2.bmLaw t k`: the laws of these two random vectors.
-/

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology ENNReal NNReal RealInnerProductSpace

namespace Math2

/-- The number of steps performed by the walk before the rescaled time `t j`. -/
