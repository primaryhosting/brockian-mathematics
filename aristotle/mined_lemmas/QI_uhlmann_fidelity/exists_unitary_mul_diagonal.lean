import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset
open scoped MatrixOrder ComplexOrder

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The dictionary between vectors of `H ⊗ H` and matrices

We model the Hilbert space `H` of a finite quantum system by `EuclideanSpace ℂ n` and the
composite system `H ⊗ H` by `EuclideanSpace ℂ (n × n)`.  A vector of the composite system is
the same thing as a matrix of coefficients. -/

/-- The matrix of coefficients of a vector of `H ⊗ H = EuclideanSpace ℂ (n × n)`. -/

lemma exists_unitary_mul_diagonal (N : Matrix n n ℂ) (s : n → ℝ)
    (hN : Nᴴ * N = diagonal (fun i => ((s i : ℝ) : ℂ)) * diagonal (fun i => ((s i : ℝ) : ℂ))) :
    ∃ W : Matrix n n ℂ, Wᴴ * W = 1 ∧ W * diagonal (fun i => ((s i : ℝ) : ℂ)) = N := by
  classical
  set col : n → EuclideanSpace ℂ n := fun j => WithLp.toLp 2 (fun i => N i j) with hcoldef
  have hcol : ∀ j k, (inner ℂ (col j) (col k) : ℂ) = if j = k then ((s j : ℂ)) ^ 2 else 0 := by
    intro j k
    have h : (inner ℂ (col j) (col k) : ℂ) = (Nᴴ * N) j k := by
      simp [hcoldef, PiLp.inner_apply, RCLike.inner_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, mul_comm]
    rw [h, hN, Matrix.diagonal_mul_diagonal]
    by_cases h' : j = k <;> simp [h', sq]
  set S : Set n := {j | s j ≠ 0} with hSdef
  set u : n → EuclideanSpace ℂ n := fun j => ((s j : ℂ))⁻¹ • col j with hudef
  have horth : Orthonormal ℂ (S.restrict u) := by
    rw [orthonormal_iff_ite]
    rintro ⟨j, hj⟩ ⟨k, hk⟩
    simp only [Set.restrict_apply, hudef, inner_smul_left, inner_smul_right, hcol]
    rw [Complex.conj_inv, Complex.conj_ofReal]
    by_cases h : j = k
    · subst h
      have hne : ((s j : ℂ)) ≠ 0 := by simpa using hj
      field_simp
      simp
    · simp [h, Subtype.ext_iff]
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq
    (by simp [finrank_euclideanSpace] : Module.finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n)
  refine ⟨Matrix.of fun i j => b j i, ?_, ?_⟩
  · ext j k
    have h1 : (inner ℂ (b j) (b k) : ℂ) = if j = k then 1 else 0 :=
      orthonormal_iff_ite.mp b.orthonormal j k
    rw [PiLp.inner_apply] at h1
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
      RCLike.inner_apply] at h1 ⊢
    rw [← h1]
    simp [mul_comm]
  · ext i j
    rw [Matrix.mul_diagonal]
    simp only [Matrix.of_apply]
    by_cases h : s j = 0
    · have h0 : col j = 0 := by
        have hc := hcol j j
        rw [if_pos rfl, h] at hc
        simpa using hc
      have hz : N i j = 0 := by
        have := congrFun (congrArg WithLp.ofLp h0) i
        simpa [hcoldef] using this
      simp [h, hz]
    · rw [hb j h]
      have hne : ((s j : ℂ)) ≠ 0 := by simpa using h
      simp [hudef, hcoldef]
      field_simp

/-- **Polar decomposition** of a square complex matrix: `M = U √(Mᴴ M)` with `U` unitary. -/
