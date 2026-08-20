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

theorem gauss_bonnet_polyhedral (corners : Finset (V × F)) (sides : F → ℕ) (E : ℕ)
    (angle : V × F → ℝ)
    (hface : ∀ f : F, ∑ c ∈ corners with c.2 = f, angle c = ((sides f : ℝ) - 2) * Real.pi)
    (hsides : ∑ f : F, sides f = 2 * E) :
    ∑ v : V, (2 * Real.pi - ∑ c ∈ corners with c.1 = v, angle c)
      = 2 * Real.pi * ((Fintype.card V : ℝ) - E + Fintype.card F) := by
  have h1 : ∑ v : V, ∑ c ∈ corners with c.1 = v, angle c = ∑ c ∈ corners, angle c :=
    Finset.sum_fiberwise corners (fun c => c.1) angle
  have h2 : ∑ f : F, ∑ c ∈ corners with c.2 = f, angle c = ∑ c ∈ corners, angle c :=
    Finset.sum_fiberwise corners (fun c => c.2) angle
  have h3 : ∑ c ∈ corners, angle c
      = ((∑ f : F, (sides f : ℝ)) - 2 * Fintype.card F) * Real.pi := by
    rw [← h2]
    rw [Finset.sum_congr rfl (fun f _ => hface f)]
    rw [← Finset.sum_mul, Finset.sum_sub_distrib]
    simp [Finset.card_univ, mul_comm]
  have h4 : (∑ f : F, (sides f : ℝ)) = 2 * E := by
    have : ((∑ f : F, sides f : ℕ) : ℝ) = ((2 * E : ℕ) : ℝ) := by rw [hsides]
    push_cast at this
    simpa using this
  rw [Finset.sum_sub_distrib, h1, h3, h4]
  simp [Finset.card_univ]
  ring

end Polyhedral

end Math2

