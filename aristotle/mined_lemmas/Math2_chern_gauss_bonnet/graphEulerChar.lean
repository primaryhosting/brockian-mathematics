/-
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real Classical
open MeasureTheory Filter Topology

namespace Math2

/-! ## The Pfaffian of the curvature (the Euler form density)

On a closed oriented Riemannian manifold `M` of even dimension `2 * n`, the Euler form is
`Pf(Ω / (2π))`, where `Ω` is the curvature two-form of the Levi-Civita connection written in a
local oriented orthonormal frame.  Expanding the Pfaffian and the wedge products in that frame,
`Pf(Ω / (2π))` is the multiple

`e(x) = 1 / ((8π)^n * n!) * ∑_{σ, τ ∈ S_{2n}} sgn σ * sgn τ *
          ∏_{i < n} R_{σ(2i) σ(2i+1) τ(2i) τ(2i+1)}(x)`

of the Riemannian volume form, where `R` denotes the components of the Riemann curvature tensor
in that frame.  We take this scalar density as the (frame-independent) definition of the
integrand of the Chern–Gauss–Bonnet theorem. -/

/-- The index `2 * i + j` of `Fin (2 * n)`, used to split `Fin (2 * n)` into `n` consecutive
pairs. -/

noncomputable def graphEulerChar (G : SimpleGraph V) : ℚ :=
  ∑ s ∈ graphSimplices G, (-1) ^ (s.card + 1)

/-- The combinatorial curvature of `G` at a vertex `v`: each simplex containing `v` contributes
its sign divided by its number of vertices. -/
