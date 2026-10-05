/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# The Knill–Laflamme theorem

A quantum code (given by the orthogonal projector `P` onto the code space) corrects an
error set `E : ι → Matrix n n ℂ` **iff** the Knill–Laflamme conditions
`P * (E i)ᴴ * (E j) * P = c i j • P` hold for some matrix of scalars `c`.
-/

namespace QI

open Matrix Finset

variable {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- The standard inner product on `n → ℂ`, conjugate linear in the first argument. -/

theorem corrects_of_kl {P : Matrix n n ℂ} (hP : IsProj P) {E : ι → Matrix n n ℂ}
    (h : KLCond P E) : Corrects P E := by
  classical
  obtain ⟨c, hc⟩ := h
  by_cases hP0 : P = 0
  · -- the trivial code: there are no unit code vectors, so any channel works
    refine corrects_of (κ := Unit) (fun _ => 1) (by simp) ?_
    intro v hv hn
    rw [hP0, Matrix.zero_mulVec] at hv
    rw [← hv, ip_zero_left] at hn
    exact absurd hn.symm one_ne_zero
  obtain ⟨u, hu, hun⟩ := exists_unit_code_vector hP hP0
  -- the matrix of Knill–Laflamme coefficients is a Gram matrix, hence Hermitian
  have hcu : ∀ i j, c i j = ip (E i *ᵥ u) (E j *ᵥ u) := by
    intro i j
    conv_rhs => rw [← hu]
    rw [← ip_sandwich hP, hc i j, smul_mulVec, hu, ip_smul_right, hun, mul_one]
  have hch : c.IsHermitian := by
    ext i j
    rw [Matrix.conjTranspose_apply, hcu, hcu, RCLike.star_def]
    exact ip_conj _ _
  set U : Matrix ι ι ℂ := (hch.eigenvectorUnitary : Matrix ι ι ℂ) with hUdef
  set d : ι → ℝ := hch.eigenvalues with hddef
  have hUU : U * Uᴴ = 1 := by
    rw [hUdef, ← Matrix.star_eq_conjTranspose]
    exact (Unitary.mem_iff.1 hch.eigenvectorUnitary.2).2
  have hUsU : Uᴴ * U = 1 := by
    rw [hUdef, ← Matrix.star_eq_conjTranspose]
    exact (Unitary.mem_iff.1 hch.eigenvectorUnitary.2).1
  -- diagonalisation of the coefficient matrix
  have hspec : Uᴴ * c * U = Matrix.diagonal (fun a => ((d a : ℝ) : ℂ)) := by
    have hs := hch.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at hs
    have key : Uᴴ * (U * Matrix.diagonal (RCLike.ofReal ∘ hch.eigenvalues) * star U) * U
        = Matrix.diagonal (fun a => ((d a : ℝ) : ℂ)) := by
      rw [← Matrix.star_eq_conjTranspose]
      rw [← Matrix.star_eq_conjTranspose] at hUsU
      simp only [← mul_assoc, hUsU]
      rw [mul_assoc, mul_assoc, hUsU]
      simp [Function.comp_def, hddef]
    rw [← hs] at key
    exact key
  -- the orthogonalised error operators
  set F : ι → Matrix n n ℂ := fun a => ∑ i, U i a • E i with hFdef
  have hFdiag : ∀ a b, P * (F a)ᴴ * F b * P
      = (if a = b then ((d a : ℝ) : ℂ) else 0) • P := by
    intro a b
    have hentry : (∑ i, ∑ j, (starRingEnd ℂ) (U i a) * U j b * c i j)
        = if a = b then ((d a : ℝ) : ℂ) else 0 := by
      rw [conj_bilin_apply, hspec, Matrix.diagonal_apply]
    rw [hFdef]
    simp only
    rw [sandwich_expand P E (fun i => U i a) (fun j => U j b)]
    simp only [hc, smul_smul, ← Finset.sum_smul]
    rw [hentry]
  have hd : ∀ a, 0 ≤ d a := by
    intro a
    have h1 : ((d a : ℝ) : ℂ) = ip (F a *ᵥ u) (F a *ᵥ u) := by
      conv_rhs => rw [← hu]
      rw [← ip_sandwich hP, hFdiag a a, if_pos rfl, smul_mulVec, hu, ip_smul_right, hun,
        mul_one]
    have h2 := ip_self_nonneg (F a *ᵥ u)
    rw [← h1] at h2
    simpa using h2
  exact corrects_of_unitary_change hUU (fun a => rfl) (corrects_of_diag hP hd hFdiag)

/-- **Knill–Laflamme theorem.**  A quantum code with orthogonal projector `P` corrects
the error set `E` if and only if the Knill–Laflamme conditions hold. -/
