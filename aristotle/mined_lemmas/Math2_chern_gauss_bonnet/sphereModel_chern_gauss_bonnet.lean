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

theorem sphereModel_chern_gauss_bonnet :
    ∫ x, sphereModel.eulerForm x ∂sphereModel.vol = 2 := by
  simpa [sphereModel] using chern_gauss_bonnet sphereModel

/-! ## An unconditional discrete Gauss–Bonnet theorem

The following is the combinatorial analogue of Gauss–Bonnet for the clique complex of a finite
simple graph (Knill).  It is proved here from scratch, without any hypotheses: the total
curvature of a finite simple graph equals the Euler characteristic of its clique complex. -/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The simplices of the clique complex of `G`: the nonempty cliques of `G`. -/
