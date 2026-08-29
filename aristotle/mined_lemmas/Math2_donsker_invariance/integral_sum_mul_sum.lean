/-
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

/-!
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Donsker's invariance principle states that the diffusively rescaled random walk built from
i.i.d. centered increments of unit variance converges in law, as a process, to Brownian motion.

Mathlib currently contains neither Brownian motion, nor weak convergence on the Skorokhod space,
nor the central limit theorem, so the functional statement cannot be phrased.  What is proved
here is the *second-order (moment) form* of the invariance principle, which is the part of the
statement that can be expressed with the available theory:

* the rescaled walk `W_n(t) = S_{⌊n t⌋} / √n` is centered;
* its covariance converges to the Brownian covariance, `E[W_n(s) W_n(t)] → min s t`;
* its increments have the Brownian variance in the limit, `E[(W_n(t) - W_n(s))²] → t - s`;
* its increments over disjoint time intervals are exactly independent.

All the limits depend only on the first two moments of the increments and not on their law —
this is the *invariance* content of the principle, isolated in
`Math2.donsker_invariance_law_independent`.
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Topology

/-- The diffusively rescaled random walk built from the increments `X`:
`rescaledWalk X n t ω = (X 0 + ⋯ + X (⌊n t⌋ - 1)) / √n`.
This is the piecewise-constant process appearing in Donsker's invariance principle. -/

lemma integral_sum_mul_sum
    (hmem : ∀ i, MemLp (X i) 2 μ) (hindep : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hvar : ∀ i, ∫ ω, (X i ω) ^ 2 ∂μ = 1) (S T : Finset ℕ) :
    ∫ ω, (∑ i ∈ S, X i ω) * (∑ j ∈ T, X j ω) ∂μ = ((S ∩ T).card : ℝ) := by
  have hexp : ∀ ω, (∑ i ∈ S, X i ω) * (∑ j ∈ T, X j ω)
      = ∑ i ∈ S, ∑ j ∈ T, X i ω * X j ω := fun ω => by rw [Finset.sum_mul_sum]
  simp_rw [hexp]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _
      (fun j _ => integrable_mul hmem i j))]
  have hterm : ∀ i ∈ S,
      ∫ ω, ∑ j ∈ T, X i ω * X j ω ∂μ = if i ∈ T then (1 : ℝ) else 0 := by
    intro i _
    rw [integral_finset_sum _ (fun j _ => integrable_mul hmem i j)]
    simp_rw [integral_mul_eq_ite hmem hindep hmean hvar i]
    rw [Finset.sum_ite_eq T i (fun _ => (1 : ℝ))]
  rw [Finset.sum_congr rfl hterm, Finset.sum_boole, Finset.filter_mem_eq_inter]

/-- The rescaled walk is centered. -/
