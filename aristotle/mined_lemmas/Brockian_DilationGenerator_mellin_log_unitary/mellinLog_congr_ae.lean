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

lemma mellinLog_congr_ae {f g : ℝ → E} (h : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] g) :
    mellinLog f =ᵐ[volume] mellinLog g := by
  have h1 : (f ∘ Real.exp) =ᵐ[volume.withDensity expDensity] (g ∘ Real.exp) :=
    measurePreserving_exp.quasiMeasurePreserving.ae_eq_comp h
  have h2 : (f ∘ Real.exp) =ᵐ[volume] (g ∘ Real.exp) :=
    h1.filter_mono volume_absolutelyContinuous_withDensity_exp.ae_le
  filter_upwards [h2] with t ht
  simp only [mellinLog, Function.comp_apply] at ht ⊢
  rw [ht]

