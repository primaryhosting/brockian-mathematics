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

import Mathlib

/-!
# Essential self-adjointness of the free Laplacian

This file proves that the free Laplacian `-Δ`, defined on the Schwartz space
`𝓢(ℝ^d, ℂ)` inside `L²(ℝ^d, ℂ)`, is essentially self-adjoint.

## Formalisation of essential self-adjointness

An unbounded operator is modelled here by a pair of linear maps `ι, A : D →ₗ[ℂ] H`
out of an abstract "domain" module `D`: `ι` is the (dense-range) inclusion of the
operator domain into the Hilbert space `H`, and `A` is the operator itself.

* `Brockian.Weyl.FreeLaplacian2.IsAdjointPair ι A u v` says that `(u, v)` belongs to the graph
  of the adjoint operator `A*`, i.e. `⟪v, ι f⟫ = ⟪u, A f⟫` for all `f` in the domain.
* `Brockian.Weyl.FreeLaplacian2.IsEssentiallySelfAdjoint ι A` says that the domain is dense,
  that `A` is symmetric, and that the adjoint `A*` is symmetric.  For a densely defined
  symmetric operator, symmetry of `A*` is the standard characterisation of essential
  self-adjointness (it is equivalent to `A* = A** = closure of A` being self-adjoint).

The abstract criterion `isEssentiallySelfAdjoint_of_dense_ranges` is von Neumann's basic
criterion: a densely defined symmetric operator with `Ran(A + i)` and `Ran(A - i)` dense is
essentially self-adjoint.

## Main results

* `Brockian.Weyl.FreeLaplacian2.fourier_freeLaplacian`: the Fourier transform conjugates the free
  Laplacian into multiplication by the symbol `4 π² ‖ξ‖²`.
* `Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier`: the free
  Laplacian on `𝓢(ℝ^d, ℂ) ⊆ L²(ℝ^d, ℂ)` is essentially self-adjoint.  The statement is
  unconditional: the Fourier-side input is supplied by `fourier_freeLaplacian`.
-/

namespace Brockian.Weyl.FreeLaplacian2

open MeasureTheory SchwartzMap Real Filter Topology
open scoped FourierTransform ComplexInnerProductSpace SchwartzMap ContDiff

noncomputable section

/-! ## An abstract criterion for essential self-adjointness -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {D : Type*} [AddCommGroup D] [Module ℂ D]

/-- `IsAdjointPair ι A u v` states that the pair `(u, v)` belongs to the graph of the adjoint
of the operator `A` with domain `ι`, that is, `⟪v, ι f⟫ = ⟪u, A f⟫` for every `f` in the
domain. -/

def IsAdjointPair (ι A : D →ₗ[ℂ] H) (u v : H) : Prop := ∀ f : D, ⟪v, ι f⟫ = ⟪u, A f⟫

/-- Essential self-adjointness of the operator `A` with domain `ι : D →ₗ[ℂ] H`:
the domain is dense, `A` is symmetric, and the adjoint `A*` (whose graph consists of the
pairs satisfying `IsAdjointPair`) is symmetric as well.  For a densely defined symmetric
operator the latter condition is equivalent to the closure of `A` being self-adjoint. -/
structure IsEssentiallySelfAdjoint (ι A : D →ₗ[ℂ] H) : Prop where
  /-- The domain of the operator is dense in the ambient Hilbert space. -/
  dense_domain : Dense (Set.range ι)
  /-- The operator is symmetric. -/
  symmetric : ∀ f g : D, ⟪A f, ι g⟫ = ⟪ι f, A g⟫
  /-- The adjoint operator is symmetric. -/
  adjoint_symmetric : ∀ u₁ v₁ u₂ v₂ : H, IsAdjointPair ι A u₁ v₁ → IsAdjointPair ι A u₂ v₂ →
    ⟪v₁, u₂⟫ = ⟪u₁, v₂⟫

/-- For a symmetric operator, `‖A g - i ι g‖² = ‖A g‖² + ‖ι g‖²`. -/
