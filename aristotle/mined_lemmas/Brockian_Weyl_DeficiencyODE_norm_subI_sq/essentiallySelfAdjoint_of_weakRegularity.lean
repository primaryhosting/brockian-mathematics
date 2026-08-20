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

theorem essentiallySelfAdjoint_of_weakRegularity (hA : Dense (A.domain : Set H))
    (hsym : A.IsFormalAdjoint A) (hreg : WeakRegularity A) : EssentiallySelfAdjoint A := by
  have hle : A ≤ A.adjoint := hsym.le_adjoint hA
  have hAd : Dense ((A.adjoint.domain : Submodule ℂ H) : Set H) :=
    hA.mono (fun z hz => hle.1 hz)
  have hsym' : A.adjoint.IsFormalAdjoint A.adjoint :=
    adjoint_isFormalAdjoint_self hA hsym hreg
  have h1 : A.adjoint ≤ A.adjoint.adjoint := hsym'.le_adjoint hAd
  have h2 : A.adjoint.adjoint ≤ A.adjoint := by
    refine LinearPMap.IsFormalAdjoint.le_adjoint hA ?_
    intro v z
    have hv : (v : H) ∈ A.adjoint.domain := hle.1 v.2
    have hvv : A v = A.adjoint ⟨(v : H), hv⟩ := hle.2 rfl
    rw [hvv]
    exact (LinearPMap.adjoint_isFormalAdjoint hAd).symm ⟨(v : H), hv⟩ z
  exact le_antisymm h2 h1

end Abstract

/-! ## A Schrödinger operator -/

/-- Spectral data for a Schrödinger operator: an orthonormal basis of eigenfunctions
(solutions of the underlying Sturm–Liouville ODE `-u'' + V u = E u`) together with the
corresponding real energy levels. -/
structure SchrodingerData (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The orthonormal basis of eigenfunctions. -/
  eigen : HilbertBasis ℕ ℂ H
  /-- The (real) energy levels. -/
  energy : ℕ → ℝ

namespace SchrodingerData

variable (D : SchrodingerData H)

