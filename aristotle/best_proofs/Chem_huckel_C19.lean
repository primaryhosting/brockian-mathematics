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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

/-!
# Hückel spectrum of the cycle `C₁₉`

We compute the spectrum of the adjacency matrix of Mathlib's cycle graph on `19` vertices
(the Hückel matrix of the annulene `C₁₉H₁₉`, with `α = 0`, `β = 1`), showing it is exactly
the set of numbers `2 * cos (2 π k / 19)` for `k = 0, …, 18`.

The vertex type `Fin 19` of `SimpleGraph.cycleGraph 19` is definitionally `ZMod 19`, and we
freely work with the ring structure of `ZMod 19` on it.  The eigenvectors are the additive
characters `j ↦ e (j * k)`, assembled into the discrete Fourier matrix `Chem.dftMatrix`.
-/

/-- The adjacency matrix of the cycle graph `C₁₉`, i.e. the Hückel matrix of `C₁₉H₁₉`
(with Coulomb integral `α = 0` and resonance integral `β = 1`). -/
noncomputable def C19adjMatrix : Matrix (ZMod 19) (ZMod 19) ℂ :=
  (SimpleGraph.cycleGraph 19).adjMatrix ℂ

lemma C19adjMatrix_apply (i j : ZMod 19) :
    C19adjMatrix i j = if i - j = 1 ∨ j - i = 1 then (1 : ℂ) else 0 := by
  simp [C19adjMatrix, SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_adj]

/-- The discrete Fourier matrix of order `19`: its `k`-th column is the eigenvector
`j ↦ exp (2 π i j k / 19)`. -/
noncomputable def dftMatrix : Matrix (ZMod 19) (ZMod 19) ℂ :=
  Matrix.of fun j k => ZMod.stdAddChar (j * k)

/-- The inverse of the discrete Fourier matrix of order `19`. -/
noncomputable def dftMatrixInv : Matrix (ZMod 19) (ZMod 19) ℂ :=
  Matrix.of fun k j => (19 : ℂ)⁻¹ * ZMod.stdAddChar (-(k * j))

/-- The diagonal matrix of eigenvalues. -/
noncomputable def eigDiag : Matrix (ZMod 19) (ZMod 19) ℂ :=
  Matrix.diagonal fun k => ZMod.stdAddChar k + ZMod.stdAddChar (-k)

/-- The value of the standard additive character of `ZMod 19` as a complex exponential. -/
lemma stdAddChar_eq_exp (k : ZMod 19) :
    ZMod.stdAddChar k = Complex.exp (2 * Real.pi * Complex.I * k.val / 19) := by
  have hc : ((k.val : ℤ) : ZMod 19) = k := by simp [ZMod.natCast_val, ZMod.cast_id]
  have h := ZMod.stdAddChar_coe (N := 19) (k.val : ℤ)
  rw [hc] at h
  rw [h]
  push_cast
  ring_nf

/-- The `k`-th eigenvalue is the real number `2 cos (2 π k / 19)`. -/
lemma stdAddChar_add_neg (k : ZMod 19) :
    ZMod.stdAddChar k + ZMod.stdAddChar (-k)
      = ((2 * Real.cos (2 * Real.pi * k.val / 19) : ℝ) : ℂ) := by
  have h1 : ZMod.stdAddChar (-k) = Complex.exp (-(2 * Real.pi * Complex.I * k.val / 19)) := by
    have h2 : ZMod.stdAddChar (-k) * ZMod.stdAddChar k = 1 := by
      rw [← ZMod.stdAddChar.map_add_eq_mul]; simp
    rw [stdAddChar_eq_exp k] at h2
    rw [Complex.exp_neg]
    exact eq_inv_of_mul_eq_one_left h2
  rw [stdAddChar_eq_exp k, h1,
    show ((2 * Real.cos (2 * Real.pi * k.val / 19) : ℝ) : ℂ)
        = 2 * Complex.cos ((2 * Real.pi * k.val / 19 : ℝ) : ℂ) by
      push_cast [Complex.ofReal_cos]; ring,
    Complex.cos]
  push_cast
  ring_nf

/-- Orthogonality of the characters of `ZMod 19`. -/
lemma sum_stdAddChar (t : ZMod 19) :
    ∑ i : ZMod 19, ZMod.stdAddChar (t * i) = if t = 0 then (19 : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar 19 h)

lemma dftMatrix_mul_inv : dftMatrix * dftMatrixInv = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [dftMatrix, dftMatrixInv, Matrix.of_apply]
  have hterm : ∀ k : ZMod 19, ZMod.stdAddChar (i * k) * ((19 : ℂ)⁻¹ * ZMod.stdAddChar (-(k * j)))
      = (19 : ℂ)⁻¹ * ZMod.stdAddChar ((i - j) * k) := by
    intro k
    rw [show (i - j) * k = i * k + -(k * j) by ring, ZMod.stdAddChar.map_add_eq_mul]
    ring
  simp only [hterm, ← Finset.mul_sum, sum_stdAddChar]
  rw [Matrix.one_apply]
  by_cases h : i = j
  · simp [h]
  · rw [if_neg (by simpa [sub_eq_zero] using h), if_neg h]
    ring

lemma inv_mul_dftMatrix : dftMatrixInv * dftMatrix = 1 :=
  mul_eq_one_comm.mp dftMatrix_mul_inv

/-- The Fourier matrix diagonalises the adjacency matrix of `C₁₉`. -/
lemma adj_mul_dftMatrix : C19adjMatrix * dftMatrix = dftMatrix * eigDiag := by
  ext i k
  rw [Matrix.mul_apply, eigDiag, Matrix.mul_diagonal]
  have hne : (i - 1 : ZMod 19) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 19) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  have key : ∀ j : ZMod 19, j ≠ i - 1 → j ≠ i + 1 → C19adjMatrix i j * dftMatrix j k = 0 := by
    intro j h1 h2
    rw [C19adjMatrix_apply, if_neg, zero_mul]
    rintro (h | h)
    · exact h1 (by linear_combination -h)
    · exact h2 (by linear_combination h)
  rw [Finset.sum_eq_add_of_mem (i - 1) (i + 1) (Finset.mem_univ _) (Finset.mem_univ _) hne
    (by intro j _ hj; exact key j hj.1 hj.2)]
  simp only [C19adjMatrix_apply, dftMatrix, Matrix.of_apply]
  rw [if_pos (by left; ring), if_pos (by right; ring),
    show (i - 1) * k = i * k + -k by ring, show (i + 1) * k = i * k + k by ring,
    ZMod.stdAddChar.map_add_eq_mul, ZMod.stdAddChar.map_add_eq_mul]
  ring

/-- The spectrum of a diagonal matrix is the range of its diagonal. -/
lemma spectrum_diagonal {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℂ) :
    spectrum ℂ (Matrix.diagonal d) = Set.range d := by
  ext μ
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, Matrix.algebraMap_eq_diagonal,
    show ((algebraMap ℂ (n → ℂ)) μ) = (fun _ => μ) from rfl, Matrix.diagonal_sub,
    Matrix.det_diagonal, isUnit_iff_ne_zero, not_ne_iff, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero, eq_comm]

/-- **Hückel spectrum of the cycle `C₁₉`.**  The eigenvalues of the adjacency matrix of the
cycle graph on `19` vertices are exactly the numbers `2 cos (2 π k / 19)` for `k = 0, …, 18`. -/
theorem huckel_C19 :
    spectrum ℂ ((SimpleGraph.cycleGraph 19).adjMatrix ℂ)
      = {z : ℂ | ∃ k : ℕ, k < 19 ∧ z = 2 * Real.cos (2 * Real.pi * k / 19)} := by
  have hunit : IsUnit dftMatrix := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact IsUnit.of_mul_eq_one _ (by
      rw [← Matrix.det_mul, dftMatrix_mul_inv, Matrix.det_one])
  obtain ⟨u, hu⟩ := hunit
  have hinv : (↑u⁻¹ : Matrix (ZMod 19) (ZMod 19) ℂ) = dftMatrixInv := by
    have : (↑u⁻¹ : Matrix (ZMod 19) (ZMod 19) ℂ) * dftMatrix = 1 := by
      rw [← hu]; exact u.inv_mul
    calc (↑u⁻¹ : Matrix (ZMod 19) (ZMod 19) ℂ)
        = (↑u⁻¹ * dftMatrix) * dftMatrixInv := by
          rw [Matrix.mul_assoc, dftMatrix_mul_inv, Matrix.mul_one]
      _ = dftMatrixInv := by rw [this, Matrix.one_mul]
  have hconj : ((SimpleGraph.cycleGraph 19).adjMatrix ℂ : Matrix (ZMod 19) (ZMod 19) ℂ)
      = (↑u : Matrix (ZMod 19) (ZMod 19) ℂ) * eigDiag * (↑u⁻¹ : Matrix (ZMod 19) (ZMod 19) ℂ) := by
    rw [hu, hinv]
    calc ((SimpleGraph.cycleGraph 19).adjMatrix ℂ : Matrix (ZMod 19) (ZMod 19) ℂ)
        = C19adjMatrix * (dftMatrix * dftMatrixInv) := by
          rw [dftMatrix_mul_inv, Matrix.mul_one]; rfl
      _ = (C19adjMatrix * dftMatrix) * dftMatrixInv := by rw [Matrix.mul_assoc]
      _ = dftMatrix * eigDiag * dftMatrixInv := by rw [adj_mul_dftMatrix]
  rw [show ((SimpleGraph.cycleGraph 19).adjMatrix ℂ : Matrix (ZMod 19) (ZMod 19) ℂ)
      = (↑u : Matrix (ZMod 19) (ZMod 19) ℂ) * eigDiag * (↑u⁻¹ : Matrix (ZMod 19) (ZMod 19) ℂ)
        from hconj, spectrum.units_conjugate, eigDiag, spectrum_diagonal]
  ext z
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k.val, ZMod.val_lt k, by dsimp only; rw [stdAddChar_add_neg k]; push_cast; ring⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨(k : ZMod 19), ?_⟩
    dsimp only
    rw [stdAddChar_add_neg, ZMod.val_natCast_of_lt hk]
    push_cast
    ring

end Chem

