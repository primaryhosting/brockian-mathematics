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

lemma avgR_tendsto (x : ℕ → ℝ)
    (hW : ∀ k : ℤ, k ≠ 0 →
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        Complex.exp (2 * π * Complex.I * k * x n)) atTop (𝓝 0)) (G : C(𝕋, ℝ)) :
    Tendsto (avgR x G) atTop (𝓝 (∫ z : 𝕋, G z ∂AddCircle.haarAddCircle)) := by
  set F : C(𝕋, ℂ) := ⟨fun z => (G z : ℂ), Complex.continuous_ofReal.comp G.continuous⟩ with hFdef
  have h := avgC_tendsto x hW F
  have hI : ∫ z : 𝕋, F z ∂AddCircle.haarAddCircle
      = ((∫ z : 𝕋, G z ∂AddCircle.haarAddCircle : ℝ) : ℂ) := by
    simp only [hFdef, ContinuousMap.coe_mk]
    exact integral_ofReal
  have hA : ∀ N, avgC x F N = ((avgR x G N : ℝ) : ℂ) := by
    intro N
    simp only [avgC, avgR, hFdef, ContinuousMap.coe_mk]
    push_cast
    ring
  rw [hI] at h
  have h' : Tendsto (fun N => ((avgR x G N : ℝ) : ℂ)) atTop
      (𝓝 ((∫ z : 𝕋, G z ∂AddCircle.haarAddCircle : ℝ) : ℂ)) := h.congr hA
  have h2 := (Complex.continuous_re.tendsto _).comp h'
  simpa [Function.comp_def] using h2

/-! ### Step C: plateau functions on the circle -/

/-- A continuous "plateau" function on the circle: it equals `1` on the closed ball of radius
`s - d` around `c`, vanishes outside the closed ball of radius `s`, and takes values in `[0,1]`. -/
