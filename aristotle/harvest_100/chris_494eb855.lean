import Mathlib

/-!
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ENNReal NNReal
open MeasureTheory Measure Module

namespace Frontier

/-- The **Gagliardo–Nirenberg(–Sobolev) interpolation inequality**.

Let `E` be a finite-dimensional real normed space of dimension `n > 0`, equipped with a Haar
measure `μ`, and let `F` be a finite-dimensional real normed space.  Fix exponents `1 ≤ p` and
`p'` with `(p')⁻¹ = p⁻¹ - n⁻¹`.  Then there is a constant `C`, depending only on `E`, `F`, `μ`
and `p` (and in particular independent of the function), such that for every compactly supported
`C¹` function `u : E → F` the `Lᵖ'` norm of `u` is bounded by `C` times the `Lᵖ` norm of its
Fréchet derivative.

The proof is by direct appeal to Mathlib's
`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq`, with the explicit constant
`MeasureTheory.SNormLESNormFDerivOfEqConst F μ p`. -/
theorem nirenberg_gagliardo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {p p' : ℝ≥0} (hp : 1 ≤ p) (hn : 0 < finrank ℝ E)
    (hp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (finrank ℝ E : ℝ)⁻¹) :
    ∃ C : ℝ≥0, ∀ u : E → F, ContDiff ℝ 1 u → HasCompactSupport u →
      eLpNorm u p' μ ≤ C * eLpNorm (fderiv ℝ u) p μ :=
  ⟨SNormLESNormFDerivOfEqConst F μ p, fun _u hu h2u ↦
    eLpNorm_le_eLpNorm_fderiv_of_eq μ hu h2u hp hn hp'⟩

end Frontier

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

