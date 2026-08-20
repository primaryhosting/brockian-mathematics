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

/-
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped InnerProductSpace ComplexConjugate ENNReal
open Filter

namespace Brockian.Weyl.DeficiencyODE

/-!
## Abstract deficiency criterion

An unbounded operator is presented here as a linear map `T` on a complex Hilbert space `H`
together with a distinguished (dense) *domain* `D`; the operator of interest is the
restriction `T|_D`.  Essential self-adjointness of a densely defined symmetric operator is
equivalent to the vanishing of both deficiency spaces `ker (T* ∓ i)`, i.e. to the density of
the ranges of `T ± i`; this is the definition used below.
-/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `T` is symmetric on the domain `D`: `⟪T x, y⟫ = ⟪x, T y⟫` for `x, y ∈ D`. -/

def IsSymmetricOn (D : Submodule ℂ H) (T : H →ₗ[ℂ] H) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ

/-- The basic (deficiency-index) criterion for essential self-adjointness of a densely
defined symmetric operator: the ranges of `T ± i` on the domain `D` are dense, equivalently
both deficiency spaces are trivial. -/
