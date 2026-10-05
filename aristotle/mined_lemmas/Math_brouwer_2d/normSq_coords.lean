import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
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

namespace Math

/-- The squared norm of a complex number, in coordinates. -/

private lemma normSq_coords (x : ℂ) : ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- **No retraction theorem** (the form needed here): there is no continuous map `g : ℂ → ℂ`
taking values in the unit circle which restricts to the identity on the unit circle.

The proof lifts `g` through the covering map `Circle.exp : ℝ → Circle`
(`Circle.isCoveringMap_exp`), which is possible because `ℂ` is simply connected and locally
path connected (`IsCoveringMap.existsUnique_continuousMap_lifts`).  The lift, evaluated along
the loop `t ↦ exp (i t)`, differs from `t` by an element of `2 π ℤ`, yet it is `2 π`-periodic;
the intermediate value theorem then produces a value in `2 π ℤ + π`, a contradiction. -/
