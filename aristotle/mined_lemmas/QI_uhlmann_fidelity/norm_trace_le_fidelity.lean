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

theorem norm_trace_le_fidelity {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {A B : Matrix n m ℂ} (hA : A * Aᴴ = ρ) (hB : B * Bᴴ = σ) :
    ‖Matrix.trace (Aᴴ * B)‖ ≤ fidelity ρ σ := by
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
  obtain ⟨V, hAV, hV, hVadj⟩ : ∃ V : Matrix n m ℂ, A = R * V ∧
      (∀ z : EuclideanSpace ℂ m, ‖Matrix.toEuclideanLin V z‖ ≤ ‖z‖) ∧
      (∀ y : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin Vᴴ y‖ ≤ ‖y‖) := by
    refine exists_contraction_of_mul_conjTranspose_eq ?_
    rw [hA, hRh, hRR]
  obtain ⟨W, hBW, hW, hWadj⟩ : ∃ W : Matrix n m ℂ, B = S * W ∧
      (∀ z : EuclideanSpace ℂ m, ‖Matrix.toEuclideanLin W z‖ ≤ ‖z‖) ∧
      (∀ y : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin Wᴴ y‖ ≤ ‖y‖) := by
    refine exists_contraction_of_mul_conjTranspose_eq ?_
    rw [hB, hSh, hSS]
  -- the overlap is `tr (M X)` for the contraction `X = V Wᴴ`
  have e : (Aᴴ * B)ᴴ = Wᴴ * (S * R * V) := by
    rw [hAV, hBW]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hRh, hSh,
      Matrix.mul_assoc]
  have hconj : Matrix.trace ((Aᴴ * B)ᴴ) = Matrix.trace (M * (V * Wᴴ)) := by
    rw [e, Matrix.trace_mul_comm, hMdef, Matrix.mul_assoc]
  have hnorm : ‖Matrix.trace (Aᴴ * B)‖ = ‖Matrix.trace (M * (V * Wᴴ))‖ := by
    rw [← hconj, Matrix.trace_conjTranspose, norm_star]
  have hX : ∀ y : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin (V * Wᴴ)ᴴ y‖ ≤ ‖y‖ := by
    intro y
    have happ : Matrix.toEuclideanLin ((V * Wᴴ)ᴴ) y
        = Matrix.toEuclideanLin W (Matrix.toEuclideanLin Vᴴ y) := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        show Matrix.toEuclideanLin (W * Vᴴ)
          = (Matrix.toEuclideanLin W).comp (Matrix.toEuclideanLin Vᴴ) from
          Matrix.toLpLin_mul 2 2 2 _ _]
      simp only [LinearMap.comp_apply]
    rw [happ]
    exact le_trans (hW _) (hVadj y)
  rw [hnorm, hfid]
  exact norm_trace_mul_contraction_le M (V * Wᴴ) hX

/-- **Uhlmann's theorem, upper bound with an arbitrary ancilla**: the overlap of any
purification of `ρ` with any purification of `σ` is at most the fidelity `F(ρ, σ)`, no
matter how large the ancilla is. -/
