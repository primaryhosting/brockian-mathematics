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

lemma inner_eigen_apply (n : ℕ) (x : D.schrodingerOperator.domain) :
    ⟪D.eigen n, D.schrodingerOperator x⟫ = (D.energy n : ℂ) * ⟪D.eigen n, (x : H)⟫ := by
  have key :
      (innerₛₗ ℂ (D.eigen n)).comp D.schrodingerOperator.toFun
        = (D.energy n : ℂ) • (innerₛₗ ℂ (D.eigen n)).comp
            (D.schrodingerOperator.domain).subtype := by
    refine (Module.Basis.span D.linearIndependent_eigen).ext (fun m => ?_)
    have h1 : (Module.Basis.span D.linearIndependent_eigen) m = D.eigenMem m := rfl
    rw [h1]
    show ⟪D.eigen n, D.schrodingerOperator (D.eigenMem m)⟫
        = (D.energy n : ℂ) * ⟪D.eigen n, ((D.eigenMem m : H))⟫
    rw [schrodingerOperator_apply_eigenMem, coe_eigenMem, inner_smul_right,
      D.inner_eigen_eigen n m]
    by_cases h : n = m
    · subst h; simp
    · simp [h]
  simpa using congrArg (fun f : D.schrodingerOperator.domain →ₗ[ℂ] ℂ => f x) key

