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

lemma norm_toEuclideanLin_conjTranspose_eq [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {A B : Matrix n m ℂ} (h : A * Aᴴ = B * Bᴴ) (x : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin Aᴴ x‖ = ‖Matrix.toEuclideanLin Bᴴ x‖ := by
  have gen : ∀ M : Matrix n m ℂ,
      (inner ℂ (Matrix.toEuclideanLin Mᴴ x) (Matrix.toEuclideanLin Mᴴ x) : ℂ)
        = inner ℂ x (Matrix.toEuclideanLin (M * Mᴴ) x) := by
    intro M
    have hadj : (Matrix.toEuclideanLin Mᴴ).adjoint = Matrix.toEuclideanLin M := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]; simp
    have hmul : Matrix.toEuclideanLin M (Matrix.toEuclideanLin Mᴴ x)
        = Matrix.toEuclideanLin (M * Mᴴ) x := by
      simp
    rw [← hmul, ← hadj, LinearMap.adjoint_inner_right]
  have key : (inner ℂ (Matrix.toEuclideanLin Aᴴ x) (Matrix.toEuclideanLin Aᴴ x) : ℂ)
      = inner ℂ (Matrix.toEuclideanLin Bᴴ x) (Matrix.toEuclideanLin Bᴴ x) := by
    rw [gen A, gen B, h]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at key
  have key' : ‖Matrix.toEuclideanLin Aᴴ x‖ ^ 2 = ‖Matrix.toEuclideanLin Bᴴ x‖ ^ 2 := by
    exact_mod_cast key
  nlinarith [norm_nonneg (Matrix.toEuclideanLin Aᴴ x), norm_nonneg (Matrix.toEuclideanLin Bᴴ x)]

/-- If `A Aᴴ = B Bᴴ` then `B = A U` for some unitary `U`. -/
