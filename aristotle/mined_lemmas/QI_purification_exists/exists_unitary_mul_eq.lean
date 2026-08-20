import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Statement: Every mixed state has a purification, unique up to isometry on the ancilla.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QI

/-!
## Setting

A state of a finite dimensional quantum system with basis indexed by `n` is a positive
semidefinite matrix `ρ : Matrix n n ℂ` of trace one.

A vector of the composite system `H ⊗ K`, where `K` is an ancilla with basis indexed by `m`,
is encoded by its matrix of coefficients `A : Matrix n m ℂ`, i.e. `A` encodes
`∑ i, ∑ j, A i j • (e i ⊗ f j)`.  With this encoding the reduced density matrix
(the partial trace over the ancilla) of the pure state `|A⟩⟨A|` is exactly `A * Aᴴ`, and the
squared norm of the vector is `∑ i, ∑ j, ‖A i j‖ ^ 2 = trace (A * Aᴴ)`.

Consequently `A` purifies `ρ` exactly when `A * Aᴴ = ρ`, and an isometry `K → K'` of ancillas
acting on the second tensor factor sends the vector `A` to `A * W`, where `W : Matrix m m' ℂ`
satisfies `W * Wᴴ = 1`.
-/

/-- `A` is a purification of the state `ρ`: the reduced density matrix (partial trace over the
ancilla) of the pure state given by the vector with coefficient matrix `A` equals `ρ`. -/

theorem exists_unitary_mul_eq {n p : Type*} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]
    (A B : Matrix n p ℂ) (h : A * Aᴴ = B * Bᴴ) :
    ∃ U : Matrix p p ℂ, U * Uᴴ = 1 ∧ A * U = B := by
  -- the maps `x ↦ Aᴴ x` and `x ↦ Bᴴ x` have the same norm profile
  have hnorms : ∀ x : EuclideanSpace ℂ n,
      ‖toEuclideanLin Aᴴ x‖ = ‖toEuclideanLin Bᴴ x‖ := by
    intro x
    have key : ∀ C : Matrix n p ℂ, (inner ℂ (toEuclideanLin Cᴴ x) (toEuclideanLin Cᴴ x) : ℂ)
        = inner ℂ x (toEuclideanLin (C * Cᴴ) x) := by
      intro C
      rw [toEuclideanLin_mul, Matrix.toEuclideanLin_conjTranspose_eq_adjoint C,
        LinearMap.adjoint_inner_left]
      rfl
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), key A, key B, h]
  obtain ⟨L, hL⟩ := exists_linearIsometry_comp_eq _ _ hnorms
  obtain ⟨U₀, hU₀⟩ : ∃ U₀ : Matrix p p ℂ, toEuclideanLin U₀ = L.toLinearMap :=
    ⟨toEuclideanLin.symm L.toLinearMap, by simp⟩
  have hstar : U₀ᴴ * U₀ = 1 := by
    apply toEuclideanLin.injective
    rw [toEuclideanLin_mul, toEuclideanLin_one, hU₀,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint U₀, hU₀]
    refine LinearMap.ext fun x => ?_
    apply ext_inner_right ℂ
    intro v
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    exact L.inner_map_map x v
  have hmul : U₀ * Aᴴ = Bᴴ := by
    apply toEuclideanLin.injective
    rw [toEuclideanLin_mul, hU₀]
    exact LinearMap.ext fun x => hL x
  refine ⟨U₀ᴴ, ?_, ?_⟩
  · rw [conjTranspose_conjTranspose, hstar]
  · have h2 := congrArg Matrix.conjTranspose hmul
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_conjTranspose] at h2

/-- If `m` injects into `m'`, there is an isometric embedding `ℂ^m → ℂ^{m'}`, given by a matrix
with orthonormal columns. -/
