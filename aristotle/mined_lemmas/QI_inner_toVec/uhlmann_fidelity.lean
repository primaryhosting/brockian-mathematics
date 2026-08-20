import Mathlib

/-!
# Uhlmann's theorem

For positive semidefinite matrices `ρ σ : Matrix n n ℂ` (density operators, not necessarily
normalized), the fidelity

`F(ρ, σ) = Tr √(√ρ σ √ρ)`

equals the maximum of `|⟪ψ, φ⟫|` over all purifications `ψ` of `ρ` and `φ` of `σ` in
`ℂⁿ ⊗ ℂⁿ ≃ EuclideanSpace ℂ (n × n)`, where the reduced density matrix of a vector `ψ` is
the partial trace over the second tensor factor.

The main result is `QI.uhlmann_fidelity`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open scoped ComplexOrder InnerProductSpace MatrixOrder

namespace QI

variable {n m : Type*} [Fintype n] [Fintype m]

/-! ### Vectorization of matrices -/

/-- The vectorization of a matrix, viewed as a vector of the Hilbert space
`EuclideanSpace ℂ (n × m) ≃ ℂⁿ ⊗ ℂᵐ`. -/

theorem uhlmann_fidelity {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    IsGreatest {x : ℝ | ∃ ψ φ : EuclideanSpace ℂ (n × n),
      IsPurification ψ ρ ∧ IsPurification φ σ ∧ x = ‖⟪ψ, φ⟫_ℂ‖} (fidelity ρ σ) := by
  set R : Matrix n n ℂ := CFC.sqrt ρ with hRdef
  set S : Matrix n n ℂ := CFC.sqrt σ with hSdef
  have hR : R.PosSemidef := (CFC.sqrt_nonneg ρ).posSemidef
  have hS : S.PosSemidef := (CFC.sqrt_nonneg σ).posSemidef
  have hRR : R * R = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  have hSS : S * S = σ := CFC.sqrt_mul_sqrt_self σ hσ.nonneg
  have hRh : Rᴴ = R := hR.isHermitian
  have hSh : Sᴴ = S := hS.isHermitian
  set M : Matrix n n ℂ := S * R with hMdef
  have habs : (CFC.abs M).PosSemidef := posSemidef_abs M
  have hfid : fidelity ρ σ = (CFC.abs M).trace.re := fidelity_eq_trace_abs ρ hσ
  obtain ⟨W, hWu, hW⟩ := exists_unitary_polar M
  have hWW : Wᴴ * W = 1 := by
    simpa [star_eq_conjTranspose] using (Unitary.mem_iff.mp hWu).1
  have hWW' : W * Wᴴ = 1 := by
    simpa [star_eq_conjTranspose] using (Unitary.mem_iff.mp hWu).2
  have htr_nonneg : ‖(CFC.abs M).trace‖ = (CFC.abs M).trace.re := by
    have h0 : (0 : ℂ) ≤ (CFC.abs M).trace := habs.trace_nonneg
    rw [Complex.eq_re_of_ofReal_le h0] at *
    simp [Complex.norm_real, abs_of_nonneg (by exact_mod_cast h0 : (0:ℝ) ≤ (CFC.abs M).trace.re)]
  constructor
  · -- the value is attained
    refine ⟨toVec (R * Wᴴ), toVec S, ?_, ?_, ?_⟩
    · rw [isPurification_toVec_iff]
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hRh]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ W R, hWW, Matrix.one_mul, hRR]
    · rw [isPurification_toVec_iff, hSh, hSS]
    · rw [inner_toVec]
      have hstar : ((R * Wᴴ)ᴴ * S) = W * (R * S) := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hRh, Matrix.mul_assoc]
      rw [hstar, hfid]
      have h1 : ((W * (R * S))ᴴ).trace = (M * Wᴴ).trace := by
        congr 1
        rw [hMdef]
        simp [Matrix.conjTranspose_mul, hRh, hSh, Matrix.mul_assoc]
      have h2 : (M * Wᴴ).trace = (CFC.abs M).trace := by
        conv_lhs => rw [hW]
        rw [Matrix.trace_mul_cycle, hWW, Matrix.one_mul]
      have h3 : ‖(W * (R * S)).trace‖ = ‖(CFC.abs M).trace‖ := by
        rw [← h2, ← h1, Matrix.trace_conjTranspose, norm_star]
      rw [h3, htr_nonneg]
  · -- the value is an upper bound
    rintro x ⟨ψ, φ, hψ, hφ, rfl⟩
    set A : Matrix n n ℂ := ofVec ψ with hA
    set B : Matrix n n ℂ := ofVec φ with hB
    have hψA : ψ = toVec A := (toVec_ofVec ψ).symm
    have hφB : φ = toVec B := (toVec_ofVec φ).symm
    have hAA : A * Aᴴ = ρ := by rw [← isPurification_toVec_iff, ← hψA]; exact hψ
    have hBB : B * Bᴴ = σ := by rw [← isPurification_toVec_iff, ← hφB]; exact hφ
    obtain ⟨U, hUu, hU⟩ := exists_unitary_of_mul_conjTranspose_eq (X := A) (Y := R)
      (by rw [hAA, ← hRR]; nth_rewrite 2 [← hRh]; rfl)
    obtain ⟨V, hVu, hV⟩ := exists_unitary_of_mul_conjTranspose_eq (X := B) (Y := S)
      (by rw [hBB, ← hSS]; nth_rewrite 2 [← hSh]; rfl)
    rw [hψA, hφB, inner_toVec, hfid]
    have key : ‖(Aᴴ * B).trace‖ = ‖(M * (U * Vᴴ)).trace‖ := by
      have h1 : (Aᴴ * B)ᴴ = Vᴴ * (S * R) * U := by
        rw [hU, hV]
        simp [Matrix.conjTranspose_mul, hRh, hSh, Matrix.mul_assoc]
      have h2 : (Vᴴ * (S * R) * U).trace = (M * (U * Vᴴ)).trace := by
        rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm, hMdef]
      rw [← h2, ← h1, Matrix.trace_conjTranspose, norm_star]
    rw [key]
    exact norm_trace_mul_unitary_le M (mul_mem hUu (Unitary.star_mem hVu))

end QI

import Mathlib
import RequestProject.Uhlmann

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
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

