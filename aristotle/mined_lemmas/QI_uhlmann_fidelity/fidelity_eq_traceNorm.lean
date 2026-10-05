import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We work with finite-dimensional quantum systems, a state on `ℂⁿ` being described by a positive
semidefinite matrix `ρ : Matrix n n ℂ`.  Its fidelity with a second state `σ` is

`F(ρ, σ) = Tr √(√ρ σ √ρ)`,

which is `QI.fidelity`.

A *purification* of `ρ` in the doubled system `ℂⁿ ⊗ ℂⁿ` is a vector `u : n × n → ℂ` whose reduced
density matrix (partial trace over the second factor) is `ρ`; this is `QI.reducedDensity`.
`QI.uhlmann_fidelity` is Uhlmann's theorem: `F(ρ, σ)` is the *greatest* value of the overlap
`|⟪u, v⟫|` as `u` ranges over the purifications of `ρ` and `v` over those of `σ`.

The proof goes through the polar decomposition of a matrix (`QI.exists_unitary_polar`, proved
here from scratch by extending a linear isometry defined on a subspace) and the variational
characterisation of the trace norm (`QI.isGreatest_traceNorm`).
-/

open scoped InnerProductSpace MatrixOrder ComplexOrder BigOperators
open Matrix

namespace QI

/-! ### An auxiliary extension lemma for linear isometries -/

/-- If `f g : E →ₗ[ℂ] E` satisfy `‖g x‖ = ‖f x‖` for all `x`, then there is a linear isometry `V`
of `E` with `V ∘ f = g`.  This is the key step in the polar decomposition. -/

lemma fidelity_eq_traceNorm {ρ σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    fidelity ρ σ = traceNorm (CFC.sqrt ρ * CFC.sqrt σ) := by
  have hRh : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ := ((CFC.sqrt_nonneg ρ).posSemidef).isHermitian
  have hSh : (CFC.sqrt σ)ᴴ = CFC.sqrt σ := ((CFC.sqrt_nonneg σ).posSemidef).isHermitian
  have hSS : CFC.sqrt σ * CFC.sqrt σ = σ := CFC.sqrt_mul_sqrt_self _ (ha := hσ.nonneg)
  have hmain : (CFC.sqrt ρ * CFC.sqrt σ) * (CFC.sqrt ρ * CFC.sqrt σ)ᴴ
      = CFC.sqrt ρ * σ * CFC.sqrt ρ := by
    rw [Matrix.conjTranspose_mul, hRh, hSh, Matrix.mul_assoc,
      ← Matrix.mul_assoc (CFC.sqrt σ) (CFC.sqrt σ), hSS, ← Matrix.mul_assoc]
  rw [fidelity, traceNorm, hmain]

/-- **Uhlmann's theorem**, in matrix form.  Writing purifications of `ρ` and `σ` as matrices
`A`, `B` with `A Aᴴ = ρ` and `B Bᴴ = σ`, the fidelity is the greatest value of `|Tr (Aᴴ B)|`. -/
