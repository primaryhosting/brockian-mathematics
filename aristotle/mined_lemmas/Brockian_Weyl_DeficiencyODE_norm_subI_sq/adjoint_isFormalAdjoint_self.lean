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

lemma adjoint_isFormalAdjoint_self (hA : Dense (A.domain : Set H)) (hsym : A.IsFormalAdjoint A)
    (hreg : WeakRegularity A) : A.adjoint.IsFormalAdjoint A.adjoint := by
  intro u w
  obtain ⟨x, hx1, hx2⟩ := exists_seq_tendsto_adjoint hA hsym hreg u
  have hfa : A.IsFormalAdjoint A.adjoint := (LinearPMap.adjoint_isFormalAdjoint hA).symm
  have h1 : Tendsto (fun n => ⟪A (x n), (w : H)⟫) atTop (𝓝 ⟪A.adjoint u, (w : H)⟫) :=
    hx2.inner tendsto_const_nhds
  have h2 : Tendsto (fun n => ⟪((x n : H)), A.adjoint w⟫) atTop (𝓝 ⟪(u : H), A.adjoint w⟫) :=
    hx1.inner tendsto_const_nhds
  have h3 : (fun n => ⟪A (x n), (w : H)⟫) = fun n => ⟪((x n : H)), A.adjoint w⟫ :=
    funext fun n => hfa (x n) w
  rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

/-- **The deficiency index criterion (von Neumann).** A densely defined symmetric operator whose
deficiency subspaces are both trivial is essentially self-adjoint. -/
