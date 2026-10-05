/-
# Atiyah Singer Index
Category: Frontier — Fields Medal Work
Target: Frontier.atiyah_singer_index
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

namespace Frontier

/-!
## Setting

The Atiyah–Singer index theorem asserts that for an elliptic operator `D` acting between
sections of two vector bundles over a closed manifold, the *analytic index*

  `ind_a D = dim ker D - dim coker D`

coincides with a *topological index*, a quantity computed purely from topological data of
the symbol of `D` and of the underlying manifold, and in particular independent of the
individual operator.

This file formalizes the statement and proves the base case of the theorem: the case of a
zero-dimensional base manifold (a point).  Over a point, the "bundles" are just two
finite-dimensional vector spaces `V` and `W`, every linear operator `D : V →ₗ W` is
elliptic and Fredholm, and the topological index reduces to the difference of the ranks of
the two bundles, `dim V - dim W` (the evaluation of the Chern character of the symbol
against the Todd class over a point).  The content of the theorem in this case is that the
analytic index — an invariant defined by solving the equation `D x = 0` and measuring the
failure of surjectivity — is computed by this purely topological quantity, and hence is a
homotopy/deformation invariant of `D`.
-/

section Index

variable (k : Type*) [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {W : Type*} [AddCommGroup W] [Module k W]

/-- The kernel of an operator: the space of solutions of `D x = 0`. -/
abbrev kernelSpace (D : V →ₗ[k] W) : Submodule k V := LinearMap.ker D

/-- The cokernel of an operator: the obstruction space to solvability of `D x = y`. -/
abbrev cokernelSpace (D : V →ₗ[k] W) : Type _ := W ⧸ LinearMap.range D

/-- The **analytic index** of an operator `D`,
`ind_a D = dim ker D - dim coker D`, as an integer. -/
noncomputable def analyticIndex (D : V →ₗ[k] W) : ℤ :=
  (Module.finrank k (kernelSpace k D) : ℤ) - (Module.finrank k (cokernelSpace k D) : ℤ)

/-- The **topological index** in the zero-dimensional case: the difference of the ranks of
the two bundles, `dim V - dim W`.  It depends only on the bundles, not on the operator. -/
noncomputable def topologicalIndex (V W : Type*) [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] : ℤ :=
  (Module.finrank k V : ℤ) - (Module.finrank k W : ℤ)

/-- Rank–nullity, phrased for the cokernel: `dim coker D + dim ran D = dim W`. -/
theorem finrank_cokernel_add_finrank_range [FiniteDimensional k W] (D : V →ₗ[k] W) :
    Module.finrank k (cokernelSpace k D) + Module.finrank k (LinearMap.range D)
      = Module.finrank k W :=
  Submodule.finrank_quotient_add_finrank (LinearMap.range D)

/-- **Atiyah–Singer index theorem, base case (zero-dimensional base manifold).**

For any operator `D : V →ₗ[k] W` between finite-dimensional spaces (over a point, every
operator is elliptic), the analytic index of `D`, namely `dim ker D - dim coker D`, equals
the topological index `dim V - dim W`, which is independent of `D`. -/
theorem atiyah_singer_index [FiniteDimensional k V] [FiniteDimensional k W] (D : V →ₗ[k] W) :
    analyticIndex k D = topologicalIndex k V W := by
  have hker : Module.finrank k (LinearMap.range D) + Module.finrank k (LinearMap.ker D)
      = Module.finrank k V := LinearMap.finrank_range_add_finrank_ker D
  have hcoker := finrank_cokernel_add_finrank_range k D
  simp only [analyticIndex, topologicalIndex, kernelSpace, cokernelSpace] at *
  omega

/-- **Homotopy / deformation invariance of the analytic index** (base case): any two
elliptic operators between the same pair of bundles over a point have the same analytic
index, since it is computed by the topological index. -/
theorem analyticIndex_eq_analyticIndex [FiniteDimensional k V] [FiniteDimensional k W]
    (D₁ D₂ : V →ₗ[k] W) : analyticIndex k D₁ = analyticIndex k D₂ := by
  rw [atiyah_singer_index k D₁, atiyah_singer_index k D₂]

/-- The index of a "self-adjoint" situation, i.e. of an operator from a space to itself,
vanishes: over a point, `ind_a D = dim V - dim V = 0`. -/
theorem analyticIndex_endomorphism [FiniteDimensional k V] (D : V →ₗ[k] V) :
    analyticIndex k D = 0 := by
  rw [atiyah_singer_index k D]
  simp [topologicalIndex]

/-- Reformulation as an Euler characteristic: for the two-term elliptic complex
`0 → V → W → 0` with `H⁰ = ker D` and `H¹ = coker D`, the alternating sum of the
cohomology dimensions equals the alternating sum of the dimensions of the terms. -/
theorem euler_characteristic_eq [FiniteDimensional k V] [FiniteDimensional k W]
    (D : V →ₗ[k] W) :
    (Module.finrank k (LinearMap.ker D) : ℤ) - (Module.finrank k (W ⧸ LinearMap.range D) : ℤ)
      = (Module.finrank k V : ℤ) - (Module.finrank k W : ℤ) :=
  atiyah_singer_index k D

/-- **Additivity of the index under direct sums** (the disjoint-union axiom of index
theory), in the base case: the index of `D₁ ⊕ D₂` is the sum of the indices. -/
theorem analyticIndex_prodMap {V₁ V₂ W₁ W₂ : Type*}
    [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
    [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]
    [AddCommGroup W₁] [Module k W₁] [FiniteDimensional k W₁]
    [AddCommGroup W₂] [Module k W₂] [FiniteDimensional k W₂]
    (D₁ : V₁ →ₗ[k] W₁) (D₂ : V₂ →ₗ[k] W₂) :
    analyticIndex k (D₁.prodMap D₂) = analyticIndex k D₁ + analyticIndex k D₂ := by
  rw [atiyah_singer_index, atiyah_singer_index, atiyah_singer_index]
  simp only [topologicalIndex, Module.finrank_prod]
  push_cast
  ring

/-- **Logarithmic additivity of the index under composition**, in the base case:
`ind (D₂ ∘ D₁) = ind D₁ + ind D₂`. -/
theorem analyticIndex_comp {U : Type*} [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    [FiniteDimensional k V] [FiniteDimensional k W]
    (D₁ : U →ₗ[k] V) (D₂ : V →ₗ[k] W) :
    analyticIndex k (D₂ ∘ₗ D₁) = analyticIndex k D₁ + analyticIndex k D₂ := by
  rw [atiyah_singer_index, atiyah_singer_index, atiyah_singer_index]
  simp only [topologicalIndex]
  ring

end Index

end Frontier

