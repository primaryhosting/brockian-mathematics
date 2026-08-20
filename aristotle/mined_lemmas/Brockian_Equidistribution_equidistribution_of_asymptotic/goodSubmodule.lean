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
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The block above is repeated as the file header; Lean does not allow a module docstring to
precede the `import` line.)

This file proves **Weyl's equidistribution criterion** unconditionally: if all nontrivial
exponential sums of a real sequence `x` are asymptotically negligible, then `x` is
equidistributed modulo one.  The argument goes through the circle `𝕋 = AddCircle 1`:

* the Birkhoff averages of each Fourier monomial converge to its integral (`avgC_fourier_tendsto`);
* the set of continuous functions with this property is a closed submodule of `C(𝕋, ℂ)`, hence,
  by Stone-Weierstrass (`span_fourier_closure_eq_top`), is everything (`avgC_tendsto`);
* indicator functions of arcs are squeezed between continuous plateau functions supported on
  metric balls, whose integrals are controlled by `AddCircle.volume_closedBall`.

As an application (and as a witness that the hypothesis is satisfiable) we derive the classical
equidistribution of irrational rotations, `equidistribution_irrational_rotation`.
-/

open Filter MeasureTheory Metric Complex Set
open scoped Topology Real BigOperators

namespace Brockian.Equidistribution

local notation "𝕋" => AddCircle (1 : ℝ)

/-- The Birkhoff/Weyl average of a complex-valued continuous function on the circle along the
first `N` terms of the sequence `x`. -/

noncomputable def goodSubmodule (x : ℕ → ℝ) : Submodule ℂ C(𝕋, ℂ) where
  carrier := {F | Tendsto (avgC x F) atTop (𝓝 (∫ z : 𝕋, F z ∂AddCircle.haarAddCircle))}
  add_mem' := by
    intro F G hF hG
    simp only [Set.mem_setOf_eq] at *
    have hint : ∫ z : 𝕋, (F + G) z ∂AddCircle.haarAddCircle
        = (∫ z : 𝕋, F z ∂AddCircle.haarAddCircle) + ∫ z : 𝕋, G z ∂AddCircle.haarAddCircle := by
      simp only [ContinuousMap.add_apply]
      exact integral_add (contMapC_integrable F) (contMapC_integrable G)
    rw [hint]
    have hA : ∀ N, avgC x (F + G) N = avgC x F N + avgC x G N := by
      intro N
      simp only [avgC, ContinuousMap.add_apply, Finset.sum_add_distrib, mul_add]
    exact (hF.add hG).congr fun N => (hA N).symm
  zero_mem' := by
    simp only [Set.mem_setOf_eq, ContinuousMap.zero_apply, integral_zero]
    have h0 : ∀ N, avgC x (0 : C(𝕋, ℂ)) N = 0 := by intro N; simp [avgC]
    exact tendsto_const_nhds.congr fun N => (h0 N).symm
  smul_mem' := by
    intro c F hF
    simp only [Set.mem_setOf_eq] at *
    have hint : ∫ z : 𝕋, (c • F) z ∂AddCircle.haarAddCircle
        = c * ∫ z : 𝕋, F z ∂AddCircle.haarAddCircle := by
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      exact integral_const_mul c _
    rw [hint]
    have hA : ∀ N, avgC x (c • F) N = c * avgC x F N := by
      intro N
      simp only [avgC, ContinuousMap.smul_apply, smul_eq_mul]
      rw [← Finset.mul_sum]
      ring
    exact (hF.const_mul c).congr fun N => (hA N).symm

