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

lemma schrodingerOperator_isFormalAdjoint :
    D.schrodingerOperator.IsFormalAdjoint D.schrodingerOperator := by
  intro x y
  have key :
      (innerₛₗ ℂ (D.schrodingerOperator x)).comp (D.schrodingerOperator.domain).subtype
        = (innerₛₗ ℂ ((x : H))).comp D.schrodingerOperator.toFun := by
    refine (Module.Basis.span D.linearIndependent_eigen).ext (fun n => ?_)
    have h1 : (Module.Basis.span D.linearIndependent_eigen) n = D.eigenMem n := rfl
    have h2 : ⟪D.schrodingerOperator x, D.eigen n⟫
        = (D.energy n : ℂ) * ⟪(x : H), D.eigen n⟫ := by
      have hc1 : ⟪D.schrodingerOperator x, D.eigen n⟫
          = starRingEnd ℂ ⟪D.eigen n, D.schrodingerOperator x⟫ := (inner_conj_symm _ _).symm
      rw [hc1, D.inner_eigen_apply n x, map_mul, inner_conj_symm]
      simp
    rw [h1]
    show ⟪D.schrodingerOperator x, ((D.eigenMem n : H))⟫
        = ⟪(x : H), D.schrodingerOperator (D.eigenMem n)⟫
    rw [schrodingerOperator_apply_eigenMem, coe_eigenMem, inner_smul_right, h2]
  simpa using congrArg (fun f : D.schrodingerOperator.domain →ₗ[ℂ] ℂ => f y) key

/-- **Discharge of the weak-regularity hypothesis.** The Schrödinger operator attached to an
orthonormal eigenbasis with real energies satisfies the Weyl limit-point condition: both of its
deficiency subspaces are trivial. -/
