/-
/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command, so the mandated header above is kept as a
-- plain comment and repeated as the module docstring below.)
-/

import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder
open scoped MatrixOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

section Defs

variable {n m : Type*}

/-- The matrix `n × m` representation of a vector `ψ` of the tensor product `H ⊗ K`,
where `H` has orthonormal basis indexed by `n` and `K` has orthonormal basis indexed by `m`. -/

theorem exists_unitary_matrix_of_isometry {m : Type*} [Fintype m] [DecidableEq m]
    (u : EuclideanSpace ℂ m →ₗᵢ[ℂ] EuclideanSpace ℂ m) :
    ∃ U : Matrix m m ℂ, U ∈ Matrix.unitaryGroup m ℂ ∧
      ∀ v : EuclideanSpace ℂ m, U *ᵥ v.ofLp = (u v).ofLp := by
  set U : Matrix m m ℂ := Matrix.of fun i j => (u (EuclideanSpace.single j (1:ℂ))).ofLp i with hU
  have hdecomp : ∀ v : EuclideanSpace ℂ m,
      v = ∑ j, v.ofLp j • (EuclideanSpace.single j (1:ℂ)) := by
    intro v
    ext i
    simp [Pi.single_apply, Finset.sum_ite_eq]
  have hmul : ∀ v : EuclideanSpace ℂ m, U *ᵥ v.ofLp = (u v).ofLp := by
    intro v
    funext i
    conv_rhs => rw [hdecomp v]
    rw [map_sum]
    simp [Matrix.mulVec, dotProduct, hU, mul_comm]
  refine ⟨U, ?_, hmul⟩
  have hstar : ∀ z : ℂ, star z = (starRingEnd ℂ) z := fun _ => rfl
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  have hinner := u.inner_map_map (EuclideanSpace.single j (1:ℂ)) (EuclideanSpace.single k (1:ℂ))
  rw [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, PiLp.inner_apply] at hinner
  simp only [RCLike.inner_apply] at hinner
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, hU, Matrix.of_apply, hstar]
  rw [Finset.sum_congr rfl fun x _ =>
    mul_comm ((starRingEnd ℂ) ((u (EuclideanSpace.single j (1:ℂ))).ofLp x))
      ((u (EuclideanSpace.single k (1:ℂ))).ofLp x), hinner]
  simp

/-- If `A Aᴴ = B Bᴴ` then the columns of `Aᴴ` and `Bᴴ` have the same lengths. -/
