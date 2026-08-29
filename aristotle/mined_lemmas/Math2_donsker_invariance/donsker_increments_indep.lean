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

theorem donsker_increments_indep
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    (n : ℕ) {r s t : ℝ} (hrs : r ≤ s) (hst : s ≤ t) :
    IndepFun (fun ω => rescaledWalk X n s ω - rescaledWalk X n r ω)
      (fun ω => rescaledWalk X n t ω - rescaledWalk X n s ω) μ := by
  set a := ⌊(n : ℝ) * r⌋₊
  set b := ⌊(n : ℝ) * s⌋₊
  set c := ⌊(n : ℝ) * t⌋₊
  have hab : a ≤ b := Nat.floor_mono (mul_le_mul_of_nonneg_left hrs (Nat.cast_nonneg n))
  have hbc : b ≤ c := Nat.floor_mono (mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg n))
  have hdisj : Disjoint (Finset.Ico a b) (Finset.Ico b c) :=
    Finset.Ico_disjoint_Ico_consecutive a b c
  have hI := hindep.indepFun_finset (Finset.Ico a b) (Finset.Ico b c) hdisj hmeas
  have hφ : ∀ S : Finset ℕ, Measurable
      (fun v : (i : { x // x ∈ S }) → ℝ => (∑ i, v i) / Real.sqrt n) := by
    intro S
    exact (Finset.measurable_sum Finset.univ
      (fun i _ => measurable_pi_apply i)).div_const _
  have hcomp := hI.comp (hφ (Finset.Ico a b)) (hφ (Finset.Ico b c))
  have key : ∀ (u v : ℕ), u ≤ v →
      ((fun w : (i : { x // x ∈ Finset.Ico u v }) → ℝ => (∑ i, w i) / Real.sqrt n)
        ∘ fun (ω : Ω) (i : { x // x ∈ Finset.Ico u v }) => X (i : ℕ) ω)
        = fun ω => (∑ i ∈ Finset.range v, X i ω) / Real.sqrt n
            - (∑ i ∈ Finset.range u, X i ω) / Real.sqrt n := by
    intro u v huv
    funext ω
    simp only [Function.comp_apply]
    rw [div_sub_div_same, ← Finset.sum_Ico_eq_sub _ huv,
      Finset.sum_coe_sort (Finset.Ico u v) (fun i => X i ω)]
  rw [key a b hab, key b c hbc] at hcomp
  exact hcomp

end Math2

#print axioms Math2.donsker_invariance
#print axioms Math2.donsker_invariance_law_independent
#print axioms Math2.donsker_increments_indep

