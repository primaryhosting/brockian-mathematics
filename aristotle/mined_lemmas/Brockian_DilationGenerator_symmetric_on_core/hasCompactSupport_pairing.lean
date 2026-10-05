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

open MeasureTheory

/-- The auxiliary function `x ↦ x · f(x) · conj(g(x))`, whose derivative is exactly the
integrand appearing in the difference of the two sides of the symmetry identity. -/

theorem hasCompactSupport_pairing {f g : ℝ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (pairing f g) := by
  refine HasCompactSupport.intro hf (fun x hx => ?_)
  simp [pairing, image_eq_zero_of_notMem_tsupport hx]

/-- **Symmetry of the Berry–Keating dilation generator on the smooth compactly supported
core of `(0, ∞)`.**

For `f, g` smooth with compact support contained in `(0, ∞)`, the operator
`A f = i · ((1/2) f + x f')` satisfies `⟪A f, g⟫ = ⟪f, A g⟫`, i.e.

`∫_{(0,∞)} (A f)(x) · conj (g x) = ∫_{(0,∞)} f x · conj ((A g)(x))`.

The proof is integration by parts: the difference of the two integrands equals
`i · d/dx (x · f(x) · conj(g(x)))`, and the integral of this exact derivative over `(0, ∞)`
vanishes because the primitive is compactly supported and vanishes at `0`.

This is symmetry on the core only; no self-adjointness claim is made.

Note: the support hypotheses `tsupport f ⊆ (0,∞)` and `tsupport g ⊆ (0,∞)` are kept because
they are part of the requested statement, but the proof does not need them (the boundary term
at `0` vanishes automatically since the primitive carries a factor of `x`). -/
