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

lemma dense_range_subI (hA : Dense (A.domain : Set H))
    (h : ∀ u : A.adjoint.domain, A.adjoint u = -Complex.I • (u : H) → (u : H) = 0) :
    Dense ((LinearMap.range (subI A) : Submodule ℂ H) : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro w hw
  rw [Submodule.mem_orthogonal] at hw
  have key : ∀ z : A.domain, ⟪(-Complex.I) • w, (z : H)⟫ = ⟪w, A z⟫ := by
    intro z
    have hz := hw (subI A z) ⟨z, rfl⟩
    rw [subI_apply, inner_sub_left, sub_eq_zero] at hz
    rw [inner_smul_left, ← inner_conj_symm w (A z), hz, inner_smul_left]
    simp [inner_conj_symm]
  obtain ⟨hwm, hval⟩ := adjoint_mem_apply hA key
  exact h ⟨w, hwm⟩ hval

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- A sequence dominated in increments by a Cauchy sequence is Cauchy. -/
