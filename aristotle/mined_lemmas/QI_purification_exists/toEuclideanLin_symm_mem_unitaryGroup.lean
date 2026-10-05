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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

open Matrix

universe u v

/-! ## Linear-algebraic preliminaries -/

/-- The inner product of two images under a matrix, expressed through `Mᴴ * M`. -/

theorem toEuclideanLin_symm_mem_unitaryGroup {m : Type*} [Fintype m] [DecidableEq m]
    (U : EuclideanSpace ℂ m →ₗᵢ[ℂ] EuclideanSpace ℂ m) :
    (Matrix.toEuclideanLin.symm U.toLinearMap) ∈ Matrix.unitaryGroup m ℂ := by
  set M := (Matrix.toEuclideanLin.symm U.toLinearMap : Matrix m m ℂ) with hM
  have hMU : Matrix.toEuclideanLin M = U.toLinearMap := by rw [hM]; simp
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  have h1 := inner_toEuclideanLin_eq M (WithLp.toLp 2 (Pi.single i 1))
    (WithLp.toLp 2 (Pi.single j 1))
  rw [hMU] at h1
  simp only [LinearIsometry.coe_toLinearMap] at h1
  rw [U.inner_map_map, EuclideanSpace.inner_eq_star_dotProduct] at h1
  rw [Matrix.star_eq_conjTranspose]
  simpa [dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    Pi.single_apply, apply_ite, eq_comm] using h1.symm

/-- Two linear maps into a finite-dimensional inner product space which induce the same
inner products differ by a linear isometry of the target. -/
