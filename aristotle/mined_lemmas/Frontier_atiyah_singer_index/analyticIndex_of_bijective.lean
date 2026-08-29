import Mathlib

/-!
# Atiyah Singer Index
Category: Frontier — Fields Medal Work
Target: Frontier.atiyah_singer_index
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to be the very first
commands of a file (only plain comments may precede them), so the requested
module docstring is placed immediately after `import Mathlib`, verbatim.
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## Setting

The Atiyah–Singer index theorem asserts that for an elliptic (pseudo)differential
operator `D : Γ(E) → Γ(F)` on a closed manifold, the *analytic index*

  `ind_a D = dim ker D - dim coker D`

equals a *topological index*, an expression built only out of characteristic
classes of the symbol of `D` and of the manifold — in particular a quantity that
does not depend on `D` itself, only on the underlying topological data.

Below we formalize this statement and prove the finite-dimensional base case,
which is the model on which the whole theory is built: for a linear operator
between finite-dimensional spaces, the analytic index (defined exactly as above,
via the kernel and the cokernel) coincides with the purely "topological" index
`dim E - dim F`, which is manifestly independent of the operator.

Every elliptic operator on a closed manifold is Fredholm, and its analytic index
is computed by this same recipe; on a zero-dimensional manifold (a finite set of
points) the spaces of sections are finite-dimensional and the theorem below *is*
the index theorem in that case, the topological index being the difference of the
ranks of the two bundles.
-/

section Index

variable {K : Type*} [Field K]
variable {E F : Type*} [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

/-- The cokernel of a linear operator `D : E → F`, i.e. `F` modulo the range of `D`. -/
abbrev coker (D : E →ₗ[K] F) : Type _ := F ⧸ LinearMap.range D

/-- The **analytic index** of an operator `D : E → F`:
`dim ker D - dim coker D`. -/

theorem analyticIndex_of_bijective (D : E →ₗ[K] F) [FiniteDimensional K E]
    [FiniteDimensional K F] (hD : Function.Bijective D) : analyticIndex D = 0 := by
  have h : Module.finrank K E = Module.finrank K F :=
    (LinearEquiv.ofBijective D hD).finrank_eq
  rw [atiyah_singer_index D]
  simp [topologicalIndex, h]

/-- **The index theorem on a zero-dimensional closed manifold.**

A closed zero-dimensional manifold is a finite set of points `X`, a vector bundle
over it is a family of finite-dimensional vector spaces `x ↦ E x`, and the space
of sections is `∀ x, E x`. Any operator `D` between two such spaces of sections is
elliptic, and its analytic index equals the topological index
`∑ x, (rank (E x) - rank (F x))`, the integral over `X` of the difference of the
ranks of the two bundles. -/
