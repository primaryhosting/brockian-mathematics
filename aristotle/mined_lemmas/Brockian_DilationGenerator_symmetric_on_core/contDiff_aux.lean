/-
# Symmetric On Core
Category: Gate1 Operator
Target: Brockian.DilationGenerator.symmetric_on_core
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian
namespace DilationGenerator

open MeasureTheory

/-- The auxiliary function `x ↦ x · f x · conj (g x)`, whose derivative packages the
integration-by-parts identity for the Berry–Keating dilation generator. -/
private noncomputable def aux (f g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (x : ℂ) * f x * starRingEnd ℂ (g x)


private theorem contDiff_aux {f g : ℝ → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) : ContDiff ℝ 1 (aux f g) := by
  have hx : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  have hgc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => starRingEnd ℂ (g t)) :=
    (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.contDiff.comp hg
  exact ((hx.mul hf).mul hgc).of_le (by exact_mod_cast le_top)

