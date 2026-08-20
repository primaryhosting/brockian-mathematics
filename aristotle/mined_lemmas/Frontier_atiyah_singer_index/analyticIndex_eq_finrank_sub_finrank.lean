import Mathlib

/-!
# Atiyah Singer Index
Category: Frontier — Fields Medal Work
Target: Frontier.atiyah_singer_index
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

namespace Frontier

open Module Polynomial

/-! ## The analytic index

The *analytic index* of an operator `D` is `dim ker D - dim coker D`.  This is the
standard Fredholm index, written here for a `ℂ`-linear map between arbitrary
`ℂ`-vector spaces; it is the meaningful invariant exactly when both the kernel and
the cokernel are finite dimensional (`Module.finrank` returns `0` on infinite
dimensional spaces). -/

/-- The analytic (Fredholm) index `dim ker D - dim coker D` of a linear operator `D`. -/

theorem analyticIndex_eq_finrank_sub_finrank {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (D : V →ₗ[ℂ] W) :
    analyticIndex D = (finrank ℂ V : ℤ) - (finrank ℂ W : ℤ) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker D
  have h2 := Submodule.finrank_quotient_add_finrank (R := ℂ) (LinearMap.range D)
  unfold analyticIndex
  omega

/-! ## The topological index on a `0`-dimensional closed manifold

A closed `0`-dimensional manifold is a finite set `M` of points.  A complex vector
bundle over it is a family `E : M → Type*` of finite dimensional complex vector
spaces, and the space of smooth sections of `E` is `∀ x, E x`.

Since the cotangent space at each point is `0`, there are *no* nonzero covectors and
hence every bundle homomorphism `D : Γ(E) → Γ(F)` is elliptic: the symbol condition
(invertibility of the principal symbol at every nonzero covector) is vacuous.  The
Atiyah–Singer topological index `∫_M ch(σ_D) · Td(TM ⊗ ℂ)` collapses, since `Td = 1`
and integration over a `0`-manifold is summation over its points, to
`∑_{x ∈ M} (rk E_x - rk F_x)`. -/

/-- The topological index of a `0`-dimensional index problem: the sum over the points
of the manifold of the difference of the ranks of the two bundles. -/
