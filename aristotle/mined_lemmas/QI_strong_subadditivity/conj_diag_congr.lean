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
