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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian
namespace DilationGenerator

/-- The pointwise product `x ↦ x · f x · conj (g x)`, whose derivative encodes the
integration-by-parts identity for the Berry–Keating dilation generator. -/

theorem integral_deriv_pairing {f g : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hfc : HasCompactSupport f) :
    ∫ x in Set.Ioi (0 : ℝ), deriv (pairing f g) x = 0 := by
  have := HasCompactSupport.integral_Ioi_deriv_eq (contDiff_pairing hf hg)
    (hasCompactSupport_pairing (f := f) (g := g) hfc) 0
  simpa [pairing] using this

/-- **Symmetry of the Berry–Keating dilation generator on the smooth compactly supported
core of `(0, ∞)`.**

For `f, g : ℝ → ℂ` smooth with compact support contained in `(0, ∞)`,
`∫ (A f) · conj g = ∫ f · conj (A g)` over `(0, ∞)`, where `A f = i·((1/2)·f + x·f')`.

This is symmetry on the core only; no self-adjointness statement is claimed.

The proof is integration by parts: the integrand difference is exactly
`i · d/dx (x · f · conj g)`, whose integral over `(0, ∞)` vanishes (the boundary term at `0`
vanishes because of the factor `x`, and at `+∞` by compact support). In particular the
hypotheses `HasCompactSupport g`, `tsupport f ⊆ Set.Ioi 0` and `tsupport g ⊆ Set.Ioi 0`,
which are part of the requested statement, turn out not to be needed. -/
