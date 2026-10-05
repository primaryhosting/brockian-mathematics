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

lemma fidelity_eq {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    fidelity ρ σ = (CFC.sqrt (CFC.sqrt σ * ρ * CFC.sqrt σ)).trace.re := by
  have hRH : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ := (CFC.sqrt_nonneg ρ).posSemidef.1
  have hSH : (CFC.sqrt σ)ᴴ = CFC.sqrt σ := (CFC.sqrt_nonneg σ).posSemidef.1
  have hRR : CFC.sqrt ρ * CFC.sqrt ρ = ρ := CFC.sqrt_mul_sqrt_self _ hρ.nonneg
  have h : (CFC.sqrt ρ * CFC.sqrt σ)ᴴ * (CFC.sqrt ρ * CFC.sqrt σ)
      = CFC.sqrt σ * ρ * CFC.sqrt σ := by
    rw [Matrix.conjTranspose_mul, hRH, hSH,
      show CFC.sqrt σ * CFC.sqrt ρ * (CFC.sqrt ρ * CFC.sqrt σ)
        = CFC.sqrt σ * (CFC.sqrt ρ * CFC.sqrt ρ) * CFC.sqrt σ from by simp [Matrix.mul_assoc],
      hRR]
  rw [fidelity, traceNorm, h]

/-! ### Elementary lemmas -/

omit [Fintype n] [DecidableEq n] in
