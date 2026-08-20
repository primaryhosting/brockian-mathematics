import Mathlib

set_option maxHeartbeats 1000000

/-!
# Purification of mixed states

A mixed state on a finite dimensional system `n` is a positive semidefinite matrix `rho` of
trace one.  A *purification* of `rho` is a unit vector `psi` on the composite system
`n × m` (system ⊗ ancilla) whose reduced density matrix (partial trace over the ancilla `m`)
is `rho`.

The main theorem `QI.purification_exists` states that

* every mixed state admits a purification (with ancilla a copy of the system), and
* any two purifications of the same mixed state are related by an isometry acting on the
  ancilla alone (in particular, for ancillas of the same dimension, by a unitary).
-/

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

section Defs

variable {n m : Type*}

/-- The matrix `A` whose `(i,k)` entry is `psi (i,k)`; this is the standard identification of a
vector of the composite system `n × m` with a linear map. -/

theorem exists_unitary_of_mul_conjTranspose_eq {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (A B : Matrix n m ℂ) (h : A * Aᴴ = B * Bᴴ) :
    ∃ U : Matrix m m ℂ, Uᴴ * U = 1 ∧ B = A * U := by
  have hmulLin : ∀ (C : Matrix n m ℂ) (x y : EuclideanSpace ℂ n),
      inner ℂ ((Matrix.toEuclideanLin Cᴴ) x) ((Matrix.toEuclideanLin Cᴴ) y)
        = inner ℂ x ((Matrix.toEuclideanLin (C * Cᴴ)) y) := by
    intro C x y
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]
    congr 1
    rw [toLpLin_mul 2 2 2 C Cᴴ]
    simp [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  have hinner : ∀ x y, inner ℂ ((Matrix.toEuclideanLin Aᴴ) x) ((Matrix.toEuclideanLin Aᴴ) y)
      = inner ℂ ((Matrix.toEuclideanLin Bᴴ) x) ((Matrix.toEuclideanLin Bᴴ) y) := by
    intro x y
    rw [hmulLin A x y, hmulLin B x y, h]
  obtain ⟨L, hL⟩ := exists_isometry_comp _ _ hinner
  set U' : Matrix m m ℂ := Matrix.toEuclideanLin.symm L.toLinearMap with hU'
  have hU'lin : Matrix.toEuclideanLin U' = L.toLinearMap := by rw [hU']; simp
  have hmul : U' * Aᴴ = Bᴴ := by
    apply Matrix.toEuclideanLin.injective
    rw [toLpLin_mul 2 2 2 U' Aᴴ, hU'lin]
    refine LinearMap.ext fun x => ?_
    simpa using hL x
  have hiso : U'ᴴ * U' = 1 := by
    apply Matrix.toEuclideanLin.injective
    rw [toLpLin_mul 2 2 2 U'ᴴ U', Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hU'lin]
    refine LinearMap.ext fun x => ?_
    have hkey : ∀ y : EuclideanSpace ℂ m,
        inner ℂ y ((LinearMap.adjoint L.toLinearMap) (L.toLinearMap x)) = inner ℂ y x := by
      intro y
      rw [LinearMap.adjoint_inner_right]
      exact L.inner_map_map y x
    have hx : (LinearMap.adjoint L.toLinearMap) (L.toLinearMap x) = x := ext_inner_left ℂ hkey
    simp only [LinearMap.coe_comp, Function.comp_apply, hx]
    simp
  refine ⟨U'ᴴ, ?_, ?_⟩
  · rw [conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp hiso
  · have h2 := congrArg Matrix.conjTranspose hmul
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_conjTranspose] at h2
    exact h2.symm

/-- The general version: if `A Aᴴ = B Bᴴ` with `B` having a larger "ancilla" index type, then
`B = A * Wᴴ` for an isometry `W`. -/
