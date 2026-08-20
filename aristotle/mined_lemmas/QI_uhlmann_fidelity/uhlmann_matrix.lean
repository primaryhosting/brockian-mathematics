/-
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Statement: Fidelity equals the maximal overlap over purifications (Uhlmann's theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Statement: Fidelity equals the maximal overlap over purifications (Uhlmann's theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Basic notions

We work with a finite dimensional quantum system with Hilbert space `EuclideanSpace ℂ n`.
States are described by positive semidefinite matrices, and a purification of a state `ρ`
on the system is a vector of the composite system `EuclideanSpace ℂ (n × m)` (the tensor
product of the system with an ancilla) whose reduced density matrix (the partial trace over
the ancilla) is `ρ`.
-/

/-- The partial trace over the second (ancilla) tensor factor. -/

theorem uhlmann_matrix {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    IsGreatest {t : ℝ | ∃ A B : Matrix n n ℂ,
      A * Aᴴ = ρ ∧ B * Bᴴ = σ ∧ t = ‖Matrix.trace (Aᴴ * B)‖} (fidelity ρ σ) := by
  set R := CFC.sqrt ρ with hRdef
  set S := CFC.sqrt σ with hSdef
  have hRh : Rᴴ = R := (CFC.sqrt_nonneg ρ).posSemidef.1
  have hSh : Sᴴ = S := (CFC.sqrt_nonneg σ).posSemidef.1
  have hRR : R * R = ρ := CFC.sqrt_mul_sqrt_self _ hρ.nonneg
  have hSS : S * S = σ := CFC.sqrt_mul_sqrt_self _ hσ.nonneg
  set M := S * R with hMdef
  have hMM : Mᴴ * M = R * σ * R := by
    rw [hMdef, Matrix.conjTranspose_mul, hRh, hSh, ← hSS]
    noncomm_ring
  have hfid : fidelity ρ σ = (Matrix.trace (CFC.sqrt (Mᴴ * M))).re := by
    rw [fidelity, hMM, ← hRdef]
  constructor
  · -- attainment
    obtain ⟨U, hU, hUeq⟩ := exists_unitary_trace_mul_eq M
    have hUstar : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
    have hUstar' : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
    refine ⟨R * U, S, ?_, ?_, ?_⟩
    · rw [Matrix.conjTranspose_mul, hRh, ← Matrix.mul_assoc, Matrix.mul_assoc R U,
        hUstar', Matrix.mul_one, hRR]
    · rw [hSh, hSS]
    · have hconj : Matrix.trace (((R * U)ᴴ * S)ᴴ) = Matrix.trace (M * U) := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hSh, hMdef,
          Matrix.mul_assoc]
      have hnorm : ‖Matrix.trace ((R * U)ᴴ * S)‖ = ‖Matrix.trace (M * U)‖ := by
        rw [← hconj, Matrix.trace_conjTranspose, norm_star]
      rw [hnorm, hUeq, hfid]
      have hpsd : (CFC.sqrt (Mᴴ * M)).PosSemidef := (CFC.sqrt_nonneg _).posSemidef
      have hle : (0 : ℂ) ≤ Matrix.trace (CFC.sqrt (Mᴴ * M)) := hpsd.trace_nonneg
      obtain ⟨h1, h2⟩ := Complex.le_def.mp hle
      rw [Complex.norm_def, Complex.normSq_apply]
      simp only [Complex.zero_re, Complex.zero_im] at h1 h2
      rw [← h2]
      simp [Real.sqrt_mul_self, h1]
  · -- upper bound
    rintro t ⟨A, B, hA, hB, rfl⟩
    obtain ⟨U, hU, hAU⟩ : ∃ U ∈ unitaryGroup n ℂ, A = R * U := by
      refine exists_unitary_of_mul_conjTranspose_eq ?_
      rw [hA, hRh, hRR]
    obtain ⟨V, hV, hBV⟩ : ∃ V ∈ unitaryGroup n ℂ, B = S * V := by
      refine exists_unitary_of_mul_conjTranspose_eq ?_
      rw [hB, hSh, hSS]
    have hVstar : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
    have hVstar' : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hV
    have hUV : (U * Vᴴ) ∈ unitaryGroup n ℂ := Submonoid.mul_mem _ hU (Unitary.star_mem hV)
    have e : (Aᴴ * B)ᴴ = Vᴴ * (S * R * U) := by
      rw [hAU, hBV]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hRh, hSh]
      noncomm_ring
    have hconj : Matrix.trace ((Aᴴ * B)ᴴ) = Matrix.trace (M * (U * Vᴴ)) := by
      rw [e, Matrix.trace_mul_comm, hMdef, Matrix.mul_assoc]
    have hnorm : ‖Matrix.trace (Aᴴ * B)‖ = ‖Matrix.trace (M * (U * Vᴴ))‖ := by
      rw [← hconj, Matrix.trace_conjTranspose, norm_star]
    rw [hnorm, hfid]
    exact norm_trace_mul_unitary_le M hUV

/-! ## Uhlmann's theorem -/

/-- **Uhlmann's theorem**: the fidelity `F(ρ, σ) = tr √(√ρ σ √ρ)` of two states equals the
maximal overlap `|⟪v, w⟫|` between purifications `v` of `ρ` and `w` of `σ` (with an ancilla
of the same dimension as the system). -/
