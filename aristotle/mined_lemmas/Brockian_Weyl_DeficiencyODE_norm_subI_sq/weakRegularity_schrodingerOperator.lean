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

theorem weakRegularity_schrodingerOperator : WeakRegularity D.schrodingerOperator := by
  have main : ∀ (c : ℂ), c.im ≠ 0 → ∀ u : D.schrodingerOperator.adjoint.domain,
      D.schrodingerOperator.adjoint u = c • (u : H) → (u : H) = 0 := by
    intro c hc u hu
    have hzero : ∀ n : ℕ, ⟪D.eigen n, (u : H)⟫ = 0 := by
      intro n
      have hfa := (LinearPMap.adjoint_isFormalAdjoint D.dense_domain) u (D.eigenMem n)
      rw [hu, schrodingerOperator_apply_eigenMem] at hfa
      simp only [coe_eigenMem] at hfa
      have h1 : (starRingEnd ℂ) c * ⟪(u : H), D.eigen n⟫
          = (D.energy n : ℂ) * ⟪(u : H), D.eigen n⟫ := by
        rw [inner_smul_left] at hfa
        rw [hfa, inner_smul_right]
      have h2 : ((starRingEnd ℂ) c - (D.energy n : ℂ)) * ⟪(u : H), D.eigen n⟫ = 0 := by
        rw [sub_mul, h1, sub_self]
      have h3 : (starRingEnd ℂ) c - (D.energy n : ℂ) ≠ 0 := by
        intro h
        apply hc
        have h5 := congrArg Complex.im h
        simp [Complex.sub_im, Complex.conj_im] at h5
        linarith
      have h4 : ⟪(u : H), D.eigen n⟫ = 0 := by
        rcases mul_eq_zero.1 h2 with h | h
        · exact absurd h h3
        · exact h
      rw [← inner_conj_symm, h4, _root_.map_zero]
    have hr : D.eigen.repr (u : H) = 0 := by
      ext n
      simp [HilbertBasis.repr_apply_apply, hzero n]
    have := congrArg D.eigen.repr.symm hr
    simpa using this
  refine ⟨main Complex.I (by simp), main (-Complex.I) (by simp)⟩

end SchrodingerData

/-- **The Schrödinger operator is essentially self-adjoint.**

The weak regularity (Weyl limit-point) hypothesis, which asserts that both deficiency subspaces
of the Schrödinger operator vanish, is discharged in
`Brockian.Weyl.DeficiencyODE.SchrodingerData.weakRegularity_schrodingerOperator`, so this
statement is unconditional. -/
