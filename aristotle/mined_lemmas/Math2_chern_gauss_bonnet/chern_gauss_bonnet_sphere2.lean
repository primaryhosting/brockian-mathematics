import Mathlib

/-!
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
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

/-!
## Scope of this formalization

The smooth Chern–Gauss–Bonnet theorem states that for a closed oriented Riemannian
manifold `M` of even dimension `2n`,
`∫_M Pf(Ω) / (2π)^n = χ(M)`,
where `Ω` is the curvature 2-form of the Levi-Civita connection and `Pf` the Pfaffian.

Mathlib (as of the version pinned by this project) contains **no** Riemannian curvature
tensor, no Levi-Civita connection, no Pfaffian of a matrix of 2-forms, no de Rham
integration over an oriented manifold and no topological Euler characteristic of a
manifold, so the smooth statement cannot even be *written* here, let alone proved.

What is formalized below is the combinatorial Chern–Gauss–Bonnet theorem
(Levitt; Knill's *Gauss–Bonnet for graphs and simplicial complexes*), which is the
exact discrete analogue and holds in every dimension, in particular for even-dimensional
closed combinatorial manifolds:

  the total curvature of a finite abstract simplicial complex, i.e. the sum over its
  vertices of the local curvature `K(v)`, equals its Euler characteristic.

Here the integral `∫_M` is replaced by the sum over vertices and the Pfaffian curvature
density by the local combinatorial curvature `K(v)`.

In addition, `Math2.gauss_bonnet_polyhedral` below records the two-dimensional
*geometric* form of the theorem for polyhedral surfaces (Descartes' angle-defect
theorem): the total angle defect of a closed polyhedral surface equals `2π · χ`,
which is the polyhedral incarnation of `∫_M K dA = 2π χ(M)` in dimension `2`.
-/

namespace Math2

section Simplicial

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The Euler characteristic of a finite abstract simplicial complex, presented as the
finite collection `X` of its (nonempty) faces:
`χ(X) = ∑_{σ ∈ X} (-1)^(dim σ) = ∑_{σ ∈ X} (-1)^(card σ - 1)`.
(For a complex with `f₀` vertices, `f₁` edges, `f₂` triangles, ... this is
`f₀ - f₁ + f₂ - ⋯`.) -/

theorem chern_gauss_bonnet_sphere2 : ∑ v : Fin 4, curvature sphere2 v = 2 := by
  rw [chern_gauss_bonnet sphere2 (by intro σ hσ; simp [sphere2] at hσ; exact hσ.1),
    eulerChar_sphere2]

end Sphere

section Polyhedral

variable {V F : Type*} [Fintype V] [Fintype F] [DecidableEq V] [DecidableEq F]

/-- **Gauss–Bonnet for closed polyhedral surfaces (Descartes' angle-defect theorem).**

Data: a finite vertex set `V`, a finite face set `F`, a finite set `corners` of
vertex–face incidences, the number `sides f` of sides of the face `f`, the number `E`
of edges, and the interior angle `angle c` at each corner `c`.

Hypotheses:
* `hface`: the interior angles of each face sum to `(sides f - 2) * π` (each face is a
  Euclidean polygon);
* `hsides`: every edge lies on exactly two faces, i.e. `∑ f, sides f = 2 * E`.

Conclusion: the total angular defect equals `2π` times the Euler characteristic
`|V| - E + |F|`.  This is the two-dimensional polyhedral form of Chern–Gauss–Bonnet,
`∫_M K dA = 2π χ(M)`. -/
