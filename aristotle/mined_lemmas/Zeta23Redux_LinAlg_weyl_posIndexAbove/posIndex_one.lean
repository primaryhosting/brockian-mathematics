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
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped BigOperators

namespace Zeta23Redux.LinAlg

section Aux

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The (real part of the) Hermitian quadratic form `x ↦ x* M x`. -/
private noncomputable def qform (M : Matrix n n ℂ) (x : n → ℂ) : ℝ := (star x ⬝ᵥ M *ᵥ x).re

/-- The squared euclidean norm of a vector. -/
private noncomputable def nsq (x : n → ℂ) : ℝ := (star x ⬝ᵥ x).re

omit [DecidableEq n] in

theorem posIndex_one : posIndex (Matrix.isHermitian_one (n := Fin d) (α := ℂ)) = d := by
  have h : ∀ i, (Matrix.isHermitian_one (n := Fin d) (α := ℂ)).eigenvalues i = 1 := by
    intro i
    have h1 := (Matrix.isHermitian_one (n := Fin d) (α := ℂ)).eigenvalues_eq i
    set b := (Matrix.isHermitian_one (n := Fin d) (α := ℂ)).eigenvectorBasis i
    have hnorm : ‖b‖ = 1 :=
      (Matrix.isHermitian_one (n := Fin d) (α := ℂ)).eigenvectorBasis.orthonormal.1 i
    have h2 : (inner ℂ b b : ℂ) = b.ofLp ⬝ᵥ star b.ofLp :=
      EuclideanSpace.inner_eq_star_dotProduct _ _
    have h3 : (inner ℂ b b : ℂ) = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hnorm]
      simp
    rw [Matrix.one_mulVec] at h1
    rw [h1, dotProduct_comm, ← h2, h3]
    simp
  simp [posIndex, posIndexAbove, h]

end Zeta23Redux.LinAlg

