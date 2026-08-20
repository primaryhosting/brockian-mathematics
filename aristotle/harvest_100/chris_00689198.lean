/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- block comment; the same header is repeated below as the module docstring.)

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Chem

open Matrix Complex

/-- The adjacency matrix of the cycle graph `C₁₇` (the Hückel matrix of the cyclic
polyene, in units where the diagonal Coulomb integral is `0` and the resonance
integral is `1`), with vertices indexed by `ZMod 17`: `i` and `j` are adjacent iff
they differ by `1`. -/
def C17adj : Matrix (ZMod 17) (ZMod 17) ℂ :=
  fun i j => if i - j = 1 ∨ j - i = 1 then 1 else 0

/-- The standard additive character `k ↦ exp (2πi k / 17)` on `ZMod 17`. -/
noncomputable def chi : AddChar (ZMod 17) ℂ := ZMod.stdAddChar

/-- The eigenvalue attached to `k : ZMod 17`, namely `2 cos (2πk/17)`. -/
noncomputable def C17eig (k : ZMod 17) : ℂ := 2 * Real.cos (2 * Real.pi * k.val / 17)

/-- The discrete Fourier matrix, whose columns are the eigenvectors of `C17adj`. -/
noncomputable def C17F : Matrix (ZMod 17) (ZMod 17) ℂ := fun j k => chi (j * k)

/-- The conjugate Fourier matrix. -/
noncomputable def C17Fbar : Matrix (ZMod 17) (ZMod 17) ℂ := fun j k => chi (-(j * k))

lemma chi_apply (k : ZMod 17) : chi k = Complex.exp (2 * π * I * k.val / 17) :=
  ZMod.toCircle_apply k

/-- `exp (2πik/17) + exp (-2πik/17) = 2 cos (2πk/17)`. -/
lemma chi_add_chi_neg (k : ZMod 17) : chi k + chi (-k) = C17eig k := by
  have h1 : chi k = Complex.exp (((2 * Real.pi * k.val / 17 : ℝ) : ℂ) * I) := by
    rw [chi, ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    push_cast
    ring_nf
  have h2 : chi (-k) = (chi k)⁻¹ := AddChar.map_neg_eq_inv _ _
  rw [h2, h1, ← Complex.exp_neg, C17eig, Complex.ofReal_cos, Complex.cos]
  ring_nf

/-- The columns of the Fourier matrix are eigenvectors of the adjacency matrix. -/
lemma C17adj_mul_C17F : C17adj * C17F = C17F * Matrix.diagonal C17eig := by
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have hne : (i - 1 : ZMod 17) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 17) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  have hiff : ∀ j : ZMod 17,
      (i - j = 1 ∨ j - i = 1) ↔ (j ∈ ({i - 1, i + 1} : Finset (ZMod 17))) := by
    intro j
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · left; linear_combination -h
      · right; linear_combination h
    · rintro (h | h)
      · left; linear_combination -h
      · right; linear_combination h
  simp only [C17adj, C17F, hiff, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_pair hne]
  have e1 : (i - 1) * k = i * k + (-k) := by ring
  have e2 : (i + 1) * k = i * k + k := by ring
  rw [e1, e2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, ← mul_add,
    add_comm (chi (-k)) (chi k), chi_add_chi_neg]

/-- Orthogonality of the additive characters of `ZMod 17`. -/
lemma chi_sum (c : ZMod 17) : ∑ k : ZMod 17, chi (c * k) = if c = 0 then (17 : ℂ) else 0 := by
  classical
  set psi : AddChar (ZMod 17) ℂ := chi.compAddMonoidHom (AddMonoidHom.mulLeft c) with hpsi
  have hval : ∀ k : ZMod 17, psi k = chi (c * k) := by intro k; simp [hpsi]
  have hzero : psi = 0 ↔ c = 0 := by
    constructor
    · intro h
      have h1 := hval 1
      rw [h] at h1
      simp only [AddChar.zero_apply, mul_one] at h1
      have h2 : chi c = chi 0 := by rw [← h1]; simp [chi]
      exact ZMod.injective_stdAddChar (N := 17) h2
    · intro h
      ext x
      simp [hval, h, chi]
  simp only [← hval]
  rw [AddChar.sum_eq_ite]
  simp [hzero]

lemma C17F_mul_C17Fbar : C17F * C17Fbar = (17 : ℂ) • (1 : Matrix (ZMod 17) (ZMod 17) ℂ) := by
  ext j l
  rw [Matrix.mul_apply]
  have hterm : ∀ k : ZMod 17, C17F j k * C17Fbar k l = chi ((j - l) * k) := by
    intro k
    rw [C17F, C17Fbar, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp only [hterm, chi_sum]
  by_cases h : j = l
  · simp [h]
  · have hjl : j - l ≠ 0 := sub_ne_zero_of_ne h
    simp [hjl, h]

lemma det_C17F_ne_zero : C17F.det ≠ 0 := by
  intro h
  have h2 := congrArg Matrix.det C17F_mul_C17Fbar
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h2
  norm_num at h2

/-- The characteristic determinant of the adjacency matrix factors over the claimed
eigenvalues. -/
lemma det_sub_C17adj (μ : ℂ) :
    (Matrix.diagonal (fun _ : ZMod 17 => μ) - C17adj).det = ∏ k : ZMod 17, (μ - C17eig k) := by
  have hcomm : (Matrix.diagonal (fun _ : ZMod 17 => μ)) * C17F
      = C17F * (Matrix.diagonal (fun _ : ZMod 17 => μ)) := by
    ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  have key : (Matrix.diagonal (fun _ : ZMod 17 => μ) - C17adj) * C17F
      = C17F * Matrix.diagonal (fun k : ZMod 17 => μ - C17eig k) := by
    rw [Matrix.sub_mul, hcomm, C17adj_mul_C17F, ← Matrix.mul_sub]
    congr 1
    rw [← Matrix.diagonal_sub]
  have h2 := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at h2
  exact mul_right_cancel₀ det_C17F_ne_zero (by rw [h2]; ring :
    (Matrix.diagonal (fun _ : ZMod 17 => μ) - C17adj).det * C17F.det
      = (∏ k : ZMod 17, (μ - C17eig k)) * C17F.det)

/-- **Hückel theory for the cycle `C₁₇`.** The spectrum of the adjacency matrix of the
cycle graph on 17 vertices consists exactly of the numbers `2 cos (2πk/17)`,
for `k = 0, 1, …, 16`. -/
theorem huckel_C17 (μ : ℂ) :
    μ ∈ spectrum ℂ C17adj ↔ ∃ k : ℕ, k < 17 ∧ μ = 2 * Real.cos (2 * Real.pi * k / 17) := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det]
  have halg : (algebraMap ℂ (Matrix (ZMod 17) (ZMod 17) ℂ)) μ
      = Matrix.diagonal (fun _ : ZMod 17 => μ) := by
    simp [Matrix.algebraMap_eq_diagonal, Pi.algebraMap_def]
  rw [halg, det_sub_C17adj, isUnit_iff_ne_zero, not_not, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    exact ⟨k.val, ZMod.val_lt k, by simpa [C17eig] using sub_eq_zero.mp hk⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨(k : ZMod 17), Finset.mem_univ _, ?_⟩
    have hv : ((k : ZMod 17)).val = k := ZMod.val_natCast_of_lt hk
    simp [C17eig, hv]

/-- Each `2 cos (2πk/17)` is realised by an explicit eigenvector, namely the
discrete-Fourier vector `j ↦ exp (2πi jk/17)`. -/
theorem huckel_C17_eigenvector (k : ZMod 17) :
    C17adj.mulVec (fun j => chi (j * k)) = C17eig k • (fun j => chi (j * k)) := by
  funext i
  have h := congrFun (congrFun C17adj_mul_C17F i) k
  rw [Matrix.mul_apply, Matrix.mul_diagonal] at h
  simpa [Matrix.mulVec, dotProduct, C17F, Pi.smul_apply, smul_eq_mul, mul_comm] using h

end Chem

