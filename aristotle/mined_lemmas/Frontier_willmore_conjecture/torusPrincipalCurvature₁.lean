import Mathlib

/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to be the very first commands of a
file, so the module documentation block above is placed immediately after `import Mathlib`.
-/

open Real Set MeasureTheory intervalIntegral

namespace Frontier

/-! ## The torus of revolution and its Willmore energy

For `0 < r < R`, the torus of revolution `T R r ⊆ ℝ³` obtained by revolving the circle of
radius `r` centred at distance `R` from the axis is parametrised by

  `(θ, φ) ↦ ((R + r cos θ) cos φ, (R + r cos θ) sin φ, r sin θ)`,  `θ, φ ∈ [0, 2π]`.

Its two principal curvatures are `1 / r` (along the meridian circle) and
`cos θ / (R + r cos θ)` (along the parallel circle), and its area element is
`r (R + r cos θ) dθ dφ`.  These classical formulas are taken as the definitions below;
the Willmore energy `∫ H² dA` is then the honest double integral of the square of the mean
curvature against the area element.
-/

/-- The principal curvature `k₁ = 1/r` of the torus of revolution, along the meridian
circle of radius `r`. -/

noncomputable def torusPrincipalCurvature₁ (r : ℝ) : ℝ := 1 / r

/-- The principal curvature `k₂ = cos θ / (R + r cos θ)` of the torus of revolution, along
the parallel circle through the point with meridian angle `θ`. -/
