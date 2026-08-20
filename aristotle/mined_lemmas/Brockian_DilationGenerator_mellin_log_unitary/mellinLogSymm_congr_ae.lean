import Mathlib

/-!
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian
namespace DilationGenerator

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The substitution `x = exp t` as an identity of Lebesgue (`ℝ≥0∞`-valued) integrals:
integrating over `(0, ∞)` is the same as integrating `exp t • ·` over all of `ℝ`. -/

lemma mellinLogSymm_congr_ae {h₁ h₂ : ℝ → E} (h : h₁ =ᵐ[volume] h₂) :
    mellinLogSymm h₁ =ᵐ[volume.restrict (Ioi (0 : ℝ))] mellinLogSymm h₂ := by
  have h1 : h₁ =ᵐ[volume.withDensity expDensity] h₂ :=
    h.filter_mono (withDensity_absolutelyContinuous (volume : Measure ℝ) expDensity).ae_le
  have h2 : (h₁ ∘ Real.log) =ᵐ[volume.restrict (Ioi (0 : ℝ))] (h₂ ∘ Real.log) :=
    measurePreserving_log.quasiMeasurePreserving.ae_eq_comp h1
  filter_upwards [h2] with x hx
  simp only [mellinLogSymm, Function.comp_apply] at hx ⊢
  rw [hx]

