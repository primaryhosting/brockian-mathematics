import Mathlib

/-!
# Symmetric On Core
Category: Gate1 Operator
Target: Brockian.DilationGenerator.symmetric_on_core
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

set_option grind.warning false

namespace Brockian
namespace DilationGenerator

open MeasureTheory Complex

/-- Auxiliary product `x ↦ x · f x · conj (g x)` whose derivative encodes the
integration-by-parts identity for the Berry–Keating dilation generator. -/

lemma integral_deriv_prodAux {f g : ℝ → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hfc : HasCompactSupport f) :
    ∫ x in Set.Ioi (0 : ℝ), deriv (prodAux f g) x = 0 := by
  have := HasCompactSupport.integral_Ioi_deriv_eq (f := prodAux f g)
    (contDiff_prodAux hf hg) (hasCompactSupport_prodAux (g := g) hfc) 0
  simpa [prodAux] using this

/-- The Berry–Keating dilation generator `A f = i·((1/2)·f + x·f')` is symmetric on the
core of smooth compactly supported functions on `(0, ∞)`.

The hypotheses `tsupport f ⊆ Set.Ioi 0` and `tsupport g ⊆ Set.Ioi 0`, which are part of the
requested statement, are not needed for the proof (the boundary term at `0` vanishes because
of the factor `x`), but they are kept since they describe the intended core. -/
