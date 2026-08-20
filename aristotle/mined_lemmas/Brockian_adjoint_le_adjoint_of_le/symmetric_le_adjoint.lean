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
# A basic criterion for essential self-adjointness

This file develops, from scratch, the classical criterion of von Neumann:

If `A` is a densely defined symmetric operator on a complex Hilbert space `H` such that the
ranges of `A + i` and `A - i` are dense — stated here in the equivalent form that a vector
orthogonal to such a range vanishes — then the adjoint `A†` is self-adjoint.  This is exactly
the statement that `A` is *essentially self-adjoint*: the closure of `A` (which is `A††`) is
self-adjoint, equivalently `A` has a unique self-adjoint extension, namely `A†`.

## Main results

* `Brockian.isSelfAdjoint_adjoint_of_denseRange`: the criterion.
* `Brockian.eq_adjoint_of_isSelfAdjoint_of_le`: uniqueness of the self-adjoint extension.
-/

open scoped ComplexInnerProductSpace
open LinearPMap

noncomputable section

namespace Brockian

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Antitonicity of the adjoint: an extension has a smaller adjoint. -/

theorem symmetric_le_adjoint {A : H →ₗ.[ℂ] H} (hdense : Dense (A.domain : Set H))
    (hsym : ∀ x y : A.domain, ⟪A x, (y : H)⟫ = ⟪(x : H), A y⟫) : A ≤ A.adjoint := by
  constructor
  · intro x hx
    exact LinearPMap.mem_adjoint_domain_of_exists _ ⟨A ⟨x, hx⟩, fun y => hsym ⟨x, hx⟩ y⟩
  · rintro ⟨x, hx⟩ ⟨x', hx'⟩ hxy
    simp only at hxy
    subst hxy
    exact (LinearPMap.adjoint_apply_eq hdense ⟨x, hx'⟩ fun y => hsym ⟨x, hx⟩ y).symm

/-- The range of `B + z`, as a submodule of `H`. -/
