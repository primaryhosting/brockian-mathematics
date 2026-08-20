/-
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Frontier

/-! ## Euclidean 3-space as `ℝ × ℝ × ℝ`

We use the plain product type and equip it with an explicit dot product and cross
product, so that all differential-geometric quantities below are literally the
classical ones. -/

/-- Ambient space `ℝ³`. -/
abbrev E3 := ℝ × ℝ × ℝ

/-- The Euclidean dot product on `ℝ³`. -/

theorem hasDerivAt_triple {f g h : ℝ → ℝ} {f' g' h' x : ℝ} (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' x) (hh : HasDerivAt h h' x) :
    HasDerivAt (fun t => ((f t, g t, h t) : E3)) (f', g', h') x :=
  hf.prodMk (hg.prodMk hh)

/-! ## The torus of revolution -/

/-- The standard immersion of the torus of revolution with centre-circle radius `R`
and tube radius `r`: `(u, v) ↦ ((R + r cos u) cos v, (R + r cos u) sin v, r sin u)`. -/
