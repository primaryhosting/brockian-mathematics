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
# Deficiency indices, Weyl's criterion and essential self-adjointness

This file develops, from first principles, the *deficiency index* (von Neumann) criterion for
essential self-adjointness of a densely defined symmetric operator on a complex Hilbert space,
and applies it to a Schrödinger operator.

## Main definitions

* `Brockian.Weyl.DeficiencyODE.EssentiallySelfAdjoint`: a densely defined operator `A` is
  essentially self-adjoint when its adjoint `A†` is self-adjoint (equivalently, when the closure
  of `A` is self-adjoint).
* `Brockian.Weyl.DeficiencyODE.WeakRegularity`: the *weak regularity* (Weyl limit-point) condition:
  both deficiency subspaces `ker (A† ∓ i)` are trivial.

## Main results

* `Brockian.Weyl.DeficiencyODE.essentiallySelfAdjoint_of_weakRegularity`: the abstract
  von Neumann criterion; a densely defined symmetric operator satisfying `WeakRegularity` is
  essentially self-adjoint.
* `Brockian.Weyl.DeficiencyODE.weakRegularity_schrodingerOperator`: the discharge of the
  weak regularity hypothesis for the Schrödinger operator attached to an orthonormal family of
  eigenfunctions with real energies.
* `Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity`: the
  resulting **unconditional** essential self-adjointness statement.
-/

noncomputable section

namespace Brockian.Weyl.DeficiencyODE

open LinearPMap Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- An operator is *essentially self-adjoint* when its adjoint is self-adjoint.
For a densely defined symmetric operator this is equivalent to the closure being self-adjoint. -/

def subI (A : H →ₗ.[ℂ] H) : A.domain →ₗ[ℂ] H :=
  A.toFun - Complex.I • A.domain.subtype

omit [CompleteSpace H] in

@[simp] lemma subI_apply (x : A.domain) : subI A x = A x - Complex.I • (x : H) := rfl

omit [CompleteSpace H] in
/-- For a symmetric operator, `‖A x - i x‖² = ‖A x‖² + ‖x‖²`. -/

lemma norm_subI_sq (hsym : A.IsFormalAdjoint A) (x : A.domain) :
    ‖subI A x‖ ^ 2 = ‖A x‖ ^ 2 + ‖(x : H)‖ ^ 2 := by
  have hre : ⟪A x, (x : H)⟫ = starRingEnd ℂ ⟪A x, (x : H)⟫ := by
    rw [inner_conj_symm]; exact hsym x x
  have him : (⟪A x, (x : H)⟫).im = 0 := by
    have h2 := congrArg Complex.im hre
    rw [Complex.conj_im] at h2
    linarith
  rw [subI_apply, @norm_sub_sq ℂ]
  simp [inner_smul_right, him, norm_smul]

omit [CompleteSpace H] in
