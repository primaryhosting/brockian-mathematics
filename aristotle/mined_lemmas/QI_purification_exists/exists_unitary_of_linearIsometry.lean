import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QI

section Defs

variable {n m : Type*}

/-- The density matrix `|ψ⟩⟨ψ|` of a state vector `ψ` of a composite system whose
product basis is indexed by `n × m`. -/

lemma exists_unitary_of_linearIsometry [Fintype m] [DecidableEq m]
    (W : EuclideanSpace ℂ m →ₗᵢ[ℂ] EuclideanSpace ℂ m) :
    ∃ U : Matrix m m ℂ, U ∈ Matrix.unitaryGroup m ℂ ∧
      ∀ x : EuclideanSpace ℂ m, Matrix.toEuclideanLin U x = W x := by
  set U : Matrix m m ℂ := Matrix.toEuclideanLin.symm W.toLinearMap with hUdef
  have hWU : ∀ x : EuclideanSpace ℂ m, Matrix.toEuclideanLin U x = W x := by
    intro x; simp [hUdef]
  have hcol : ∀ j i, (W (EuclideanSpace.single j (1:ℂ))).ofLp i = U i j := by
    intro j i
    rw [← hWU (EuclideanSpace.single j (1:ℂ))]
    simp
  refine ⟨U, ?_, hWU⟩
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  have key : (inner ℂ (W (EuclideanSpace.single i (1:ℂ))) (W (EuclideanSpace.single j (1:ℂ))) : ℂ)
      = inner ℂ (EuclideanSpace.single i (1:ℂ)) (EuclideanSpace.single j (1:ℂ)) :=
    W.inner_map_map _ _
  rw [PiLp.inner_apply] at key
  simp only [hcol, RCLike.inner_apply] at key
  rw [Matrix.mul_apply]
  have key2 : ∑ x, (star U) i x * U x j
      = inner ℂ (EuclideanSpace.single i (1:ℂ)) (EuclideanSpace.single j (1:ℂ)) := by
    rw [← key]
    exact Finset.sum_congr rfl fun x _ => by simp [Matrix.star_apply, RCLike.star_def, mul_comm]
  rw [key2]
  simp [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, Matrix.one_apply]

