/-
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Real

namespace Frontier

/-! ## Vector algebra in `ℝ³`

We model `ℝ³` as `ℝ × ℝ × ℝ` and use the standard dot and cross products. -/

/-- The cross product of two vectors in `ℝ³`. -/

def dot3 (a b : ℝ × ℝ × ℝ) : ℝ := a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

/-! ## The two-band Bloch Hamiltonian

For a two-band Bloch Hamiltonian `H(k) = d(k) · σ` with a nowhere-vanishing vector field `d`,
the Berry curvature of the lower band is
`F = (1/2) d̂ · (∂₁ d̂ × ∂₂ d̂)`, and the Chern number is `(1/4π) ∫ d̂ · (∂₁ d̂ × ∂₂ d̂)`,
i.e. the degree of the map `d̂` into the unit sphere.

Here we take the base case in which `d̂` is the identity (degree-one) parametrisation of the
unit sphere by spherical coordinates `(θ, φ)`. -/

/-- The normalised `d`-vector of the model, in spherical coordinates. -/
