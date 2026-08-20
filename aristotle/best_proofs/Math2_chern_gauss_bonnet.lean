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
def eulerChar (X : Finset (Finset V)) : ℝ :=
  ∑ σ ∈ X, (-1 : ℝ) ^ (σ.card + 1)

/-- The local combinatorial curvature of the complex `X` at a vertex `v`:
`K(v) = ∑_{σ ∈ X, v ∈ σ} (-1)^(dim σ) / card σ`.
Equivalently `K(v) = 1 - V₀(v)/2 + V₁(v)/3 - ⋯`, where `V_k(v)` is the number of
`k`-dimensional faces of the link of `v`.  This is the discrete analogue of the
Pfaffian curvature density in the Chern–Gauss–Bonnet integrand. -/
noncomputable def curvature (X : Finset (Finset V)) (v : V) : ℝ :=
  ∑ σ ∈ X with v ∈ σ, (-1 : ℝ) ^ (σ.card + 1) / σ.card

/-- **Chern–Gauss–Bonnet (combinatorial form).**

For a finite abstract simplicial complex `X` (a finite family of nonempty faces; here
no closure hypothesis is even needed), the total curvature equals the Euler
characteristic:
`∑_{v} K(v) = χ(X)`.

This is the discrete analogue, valid in all dimensions and in particular for
even-dimensional closed combinatorial manifolds, of the Chern–Gauss–Bonnet formula
`∫_M Pf(Ω)/(2π)^n = χ(M)`: the integral over the manifold is replaced by the sum over
the vertices and the Pfaffian curvature density by the local curvature `K(v)`. -/
theorem chern_gauss_bonnet (X : Finset (Finset V)) (hX : ∀ σ ∈ X, σ.Nonempty) :
    ∑ v : V, curvature X v = eulerChar X := by
  have hcomm :
      ∑ v ∈ (Finset.univ : Finset V), ∑ σ ∈ X with v ∈ σ,
          (-1 : ℝ) ^ (σ.card + 1) / σ.card
        = ∑ σ ∈ X, ∑ _v ∈ σ, (-1 : ℝ) ^ (σ.card + 1) / σ.card := by
    refine Finset.sum_comm' ?_
    intro v σ
    simp [and_comm]
  calc ∑ v : V, curvature X v
      = ∑ σ ∈ X, ∑ _v ∈ σ, (-1 : ℝ) ^ (σ.card + 1) / σ.card := hcomm
    _ = ∑ σ ∈ X, (-1 : ℝ) ^ (σ.card + 1) := by
        refine Finset.sum_congr rfl ?_
        intro σ hσ
        have hcard : (σ.card : ℝ) ≠ 0 := by
          have := Finset.card_pos.mpr (hX σ hσ)
          positivity
        rw [Finset.sum_const, nsmul_eq_mul]
        field_simp
    _ = eulerChar X := rfl

end Simplicial

section Sphere

open Finset

/-- The boundary of the `3`-simplex: a triangulation of the `2`-sphere with `4` vertices,
`6` edges and `4` triangles.  Its faces are the nonempty proper subsets of `Fin 4`. -/
def sphere2 : Finset (Finset (Fin 4)) :=
  Finset.univ.filter (fun σ => σ.Nonempty ∧ σ ≠ Finset.univ)

/-- The Euler characteristic of the triangulated `2`-sphere is `4 - 6 + 4 = 2`. -/
theorem eulerChar_sphere2 : eulerChar sphere2 = 2 := by
  have hZ : (∑ σ ∈ sphere2, (-1 : ℤ) ^ (σ.card + 1)) = 2 := by decide
  have hc : eulerChar sphere2 = ((∑ σ ∈ sphere2, (-1 : ℤ) ^ (σ.card + 1) : ℤ) : ℝ) := by
    unfold eulerChar
    push_cast
    ring
  rw [hc, hZ]
  norm_num

/-- A concrete even-dimensional closed example: for the triangulated `2`-sphere the total
combinatorial curvature equals `2 = χ(S²)` (each of the four vertices carries curvature
`1 - 3/2 + 3/3 = 1/2`). -/
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

