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

theorem eq_zero_of_isAdjointPair_smul_I (ι A : D →ₗ[ℂ] H)
    (hd : Dense (Set.range (A + Complex.I • ι))) {x : H}
    (hx : IsAdjointPair ι A x (Complex.I • x)) : x = 0 := by
  have hsub : Set.range (A + Complex.I • ι) ⊆ {y : H | ⟪x, y⟫ = 0} := by
    rintro _ ⟨f, rfl⟩
    have h1 : ⟪Complex.I • x, ι f⟫ = ⟪x, A f⟫ := hx f
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Set.mem_setOf_eq]
    rw [inner_add_right, inner_smul_right, ← h1, inner_smul_left]
    simp
  have hcl : IsClosed {y : H | ⟪x, y⟫ = (0 : ℂ)} :=
    isClosed_eq (innerSL ℂ x).continuous continuous_const
  have huniv : (Set.univ : Set H) ⊆ {y : H | ⟪x, y⟫ = 0} := by
    rw [← hd.closure_eq]; exact hcl.closure_subset_iff.mpr hsub
  exact inner_self_eq_zero.mp (huniv (Set.mem_univ x))

variable [CompleteSpace H]

/-- Under the hypotheses of von Neumann's basic criterion, every point of the graph of the
adjoint is a limit of points of the graph of the operator. -/
