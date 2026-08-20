import Mathlib

/-!
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

open scoped BigOperators ComplexOrder
open Matrix

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Part I: Functional calculus for Hermitian matrices -/

theorem diag_fun_commute {W : Matrix n n ℂ} {μ ν : n → ℝ} (f : ℝ → ℝ)
    (h : W * diagonal (fun i => ((μ i : ℝ) : ℂ)) = diagonal (fun i => ((ν i : ℝ) : ℂ)) * W) :
    W * diagonal (fun i => ((f (μ i) : ℝ) : ℂ)) = diagonal (fun i => ((f (ν i) : ℝ) : ℂ)) * W := by
  ext i j
  have hij : W i j * (μ j : ℂ) = W i j * (ν i : ℂ) := by
    have := congrFun (congrFun h i) j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm] using this
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases eq_or_ne (W i j) 0 with hw | hw
  · simp [hw]
  · have h3 : μ j = ν i := by exact_mod_cast mul_left_cancel₀ hw hij
    rw [h3, mul_comm]

/-- Functional calculus is independent of the chosen spectral decomposition. -/
theorem conj_diag_congr {U V : Matrix n n ℂ} {μ ν : n → ℝ} (f : ℝ → ℝ)
    (hU : U ∈ unitaryGroup n ℂ) (hV : V ∈ unitaryGroup n ℂ)
    (h : U * diagonal (fun i => ((μ i : ℝ) : ℂ)) * star U
       = V * diagonal (fun i => ((ν i : ℝ) : ℂ)) * star V) :
    U * diagonal (fun i => ((f (μ i) : ℝ) : ℂ)) * star U
      = V * diagonal (fun i => ((f (ν i) : ℝ) : ℂ)) * star V := by
  have hUs : star U * U = 1 := mem_unitaryGroup_iff'.mp hU
  have hUs' : U * star U = 1 := mem_unitaryGroup_iff.mp hU
  have hVs : star V * V = 1 := mem_unitaryGroup_iff'.mp hV
  have hVs' : V * star V = 1 := mem_unitaryGroup_iff.mp hV
  obtain ⟨W, hWs, hWs', hVW⟩ :
      ∃ W : Matrix n n ℂ, star W * W = 1 ∧ W * star W = 1 ∧ V * W = U := by
    refine ⟨star V * U, ?_, ?_, ?_⟩
    · rw [Matrix.star_mul, star_star]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc V (star V) U, hVs', Matrix.one_mul, hUs]
    · rw [Matrix.star_mul, star_star]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U (star U) V, hUs', Matrix.one_mul, hVs]
    · rw [← Matrix.mul_assoc, hVs', Matrix.one_mul]
  have cV' : ∀ X : Matrix n n ℂ, star V * (V * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hVs, Matrix.one_mul]
  have key : W * diagonal (fun i => ((μ i : ℝ) : ℂ)) * star W
      = diagonal (fun i => ((ν i : ℝ) : ℂ)) := by
    have h2 := congrArg (fun X => star V * X * V) h
    simp only [← hVW, Matrix.star_mul, Matrix.mul_assoc, cV', hVs, Matrix.mul_one] at h2 ⊢
    exact h2
  have hcomm : W * diagonal (fun i => ((μ i : ℝ) : ℂ))
      = diagonal (fun i => ((ν i : ℝ) : ℂ)) * W := by
    have h5 := congrArg (fun X => X * W) key
    simp only [Matrix.mul_assoc, hWs, Matrix.mul_one] at h5 ⊢
    exact h5
  have hcomm2 := diag_fun_commute f hcomm
  have hkey2 : W * diagonal (fun i => ((f (μ i) : ℝ) : ℂ)) * star W
      = diagonal (fun i => ((f (ν i) : ℝ) : ℂ)) := by
    have h6 := congrArg (fun X => X * star W) hcomm2
    simp only [Matrix.mul_assoc, hWs', Matrix.mul_one] at h6 ⊢
    exact h6
  simp only [← hVW, Matrix.star_mul, Matrix.mul_assoc]
  rw [← hkey2]
  simp only [Matrix.mul_assoc]

omit [Fintype n] [DecidableEq n] in
theorem star_ofReal_fun (μ : n → ℝ) :
    (star fun i => ((μ i : ℝ) : ℂ)) = fun i => ((μ i : ℝ) : ℂ) := by
  ext i; simp

theorem isHermitian_of_spectral {M U : Matrix n n ℂ} {μ : n → ℝ}
    (hM : M = U * diagonal (fun i => ((μ i : ℝ) : ℂ)) * star U) : M.IsHermitian := by
  unfold Matrix.IsHermitian
  rw [hM]
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc, diagonal_conjTranspose,
    Matrix.star_eq_conjTranspose, star_ofReal_fun]

theorem spectral_decomp {M : Matrix n n ℂ} (h : M.IsHermitian) :
    M = (h.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i => ((h.eigenvalues i : ℝ) : ℂ)) *
      star (h.eigenvectorUnitary : Matrix n n ℂ) := by
  simpa [Unitary.conjStarAlgAut, Function.comp_def] using h.spectral_theorem

/-- Functional calculus for Hermitian matrices: `hfun f M` applies the real function `f`
to the eigenvalues of `M` (junk value `0` if `M` is not Hermitian). -/
noncomputable def hfun (f : ℝ → ℝ) (M : Matrix n n ℂ) : Matrix n n ℂ :=
  if h : M.IsHermitian then
    (h.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i => ((f (h.eigenvalues i) : ℝ) : ℂ)) *
      star (h.eigenvectorUnitary : Matrix n n ℂ)
  else 0

/-- `hfun` computed from an arbitrary spectral decomposition. -/
theorem hfun_spec (f : ℝ → ℝ) {M U : Matrix n n ℂ} {μ : n → ℝ}
    (hU : U ∈ unitaryGroup n ℂ)
    (hM : M = U * diagonal (fun i => ((μ i : ℝ) : ℂ)) * star U) :
    hfun f M = U * diagonal (fun i => ((f (μ i) : ℝ) : ℂ)) * star U := by
  have hHerm : M.IsHermitian := isHermitian_of_spectral hM
  rw [hfun, dif_pos hHerm]
  refine (conj_diag_congr f (hHerm.eigenvectorUnitary).2 hU ?_).symm
  rw [← spectral_decomp hHerm, hM]

/-- The matrix logarithm of a Hermitian matrix (with the convention `log 0 = 0`). -/
noncomputable def logm (M : Matrix n n ℂ) : Matrix n n ℂ := hfun Real.log M

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)`. -/
noncomputable def entropy (M : Matrix n n ℂ) : ℝ := -(Matrix.trace (M * logm M)).re

end QI

