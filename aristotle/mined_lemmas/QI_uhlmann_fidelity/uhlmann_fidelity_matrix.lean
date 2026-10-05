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

theorem uhlmann_fidelity_matrix {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    IsGreatest {r : ℝ | ∃ A B : Matrix n n ℂ, A * Aᴴ = ρ ∧ B * Bᴴ = σ ∧ r = ‖(Aᴴ * B).trace‖}
      (fidelity ρ σ) := by
  have hRh : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ := ((CFC.sqrt_nonneg ρ).posSemidef).isHermitian
  have hSh : (CFC.sqrt σ)ᴴ = CFC.sqrt σ := ((CFC.sqrt_nonneg σ).posSemidef).isHermitian
  have hRR : CFC.sqrt ρ * CFC.sqrt ρ = ρ := CFC.sqrt_mul_sqrt_self _ (ha := hρ.nonneg)
  have hSS : CFC.sqrt σ * CFC.sqrt σ = σ := CFC.sqrt_mul_sqrt_self _ (ha := hσ.nonneg)
  have hfid : fidelity ρ σ = traceNorm (CFC.sqrt ρ * CFC.sqrt σ) := fidelity_eq_traceNorm hσ
  obtain ⟨hmem, hub⟩ := isGreatest_traceNorm (CFC.sqrt ρ * CFC.sqrt σ)
  constructor
  · obtain ⟨W, hW, hWeq⟩ := hmem
    have hWWh : W * Wᴴ = 1 := by
      rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp hW
    refine ⟨CFC.sqrt ρ, CFC.sqrt σ * W, by rw [hRh, hRR], ?_, ?_⟩
    · rw [Matrix.conjTranspose_mul, hSh, Matrix.mul_assoc,
        ← Matrix.mul_assoc W Wᴴ (CFC.sqrt σ), hWWh, Matrix.one_mul, hSS]
    · rw [hfid, hWeq, hRh, ← Matrix.mul_assoc, Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  · rintro r ⟨A, B, hA, hB, rfl⟩
    obtain ⟨U₁, hU₁, hAU⟩ := exists_unitary_polar A
    obtain ⟨U₂, hU₂, hBU⟩ := exists_unitary_polar B
    rw [hA] at hAU
    rw [hB] at hBU
    have hkey : (Aᴴ * B).trace = ((U₂ * U₁ᴴ) * (CFC.sqrt ρ * CFC.sqrt σ)).trace := by
      rw [hAU, hBU, Matrix.conjTranspose_mul, hRh, Matrix.mul_assoc,
        ← Matrix.mul_assoc (CFC.sqrt ρ) (CFC.sqrt σ) U₂, ← Matrix.mul_assoc,
        Matrix.trace_mul_cycle]
    rw [hkey, hfid]
    refine hub ⟨U₂ * U₁ᴴ, Submonoid.mul_mem _ hU₂ ?_, rfl⟩
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem hU₁

/-! ### Purifications -/

/-- The overlap `⟪u, v⟫` of two bipartite pure states of `ℂⁿ ⊗ ℂⁿ`, written in coordinates. -/
