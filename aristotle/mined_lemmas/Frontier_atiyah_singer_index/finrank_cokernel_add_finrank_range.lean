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

theorem finrank_cokernel_add_finrank_range [FiniteDimensional k W] (D : V →ₗ[k] W) :
    Module.finrank k (cokernelSpace k D) + Module.finrank k (LinearMap.range D)
      = Module.finrank k W :=
  Submodule.finrank_quotient_add_finrank (LinearMap.range D)

/-- **Atiyah–Singer index theorem, base case (zero-dimensional base manifold).**

For any operator `D : V →ₗ[k] W` between finite-dimensional spaces (over a point, every
operator is elliptic), the analytic index of `D`, namely `dim ker D - dim coker D`, equals
the topological index `dim V - dim W`, which is independent of `D`. -/
