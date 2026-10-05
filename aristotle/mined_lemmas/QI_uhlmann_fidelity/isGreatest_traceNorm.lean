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

theorem isGreatest_traceNorm (M : Matrix n n ℂ) :
    IsGreatest {r : ℝ | ∃ W ∈ Matrix.unitaryGroup n ℂ, r = ‖(W * M).trace‖} (traceNorm M) := by
  set P := CFC.sqrt (M * Mᴴ) with hPdef
  obtain ⟨V, hV, hMV⟩ := exists_unitary_polar M
  have hP : P.PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hPh : Pᴴ = P := hP.isHermitian
  have htrnn : (0 : ℂ) ≤ P.trace := hP.trace_nonneg
  have htN : traceNorm M = P.trace.re := rfl
  have htr : P.trace = ((P.trace.re : ℝ) : ℂ) := Complex.eq_re_of_ofReal_le htrnn
  have htrre : 0 ≤ P.trace.re := (Complex.le_def.mp htrnn).1
  have hVV : V * Vᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp hV
  constructor
  · refine ⟨Vᴴ, by rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mem hV, ?_⟩
    have hkey : (Vᴴ * M).trace = P.trace := by
      rw [hMV, ← Matrix.mul_assoc, Matrix.trace_mul_cycle, hVV, Matrix.one_mul]
    rw [hkey, htN, htr, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htrre]
    exact Complex.ofReal_re _
  · rintro r ⟨W, hW, rfl⟩
    set S := CFC.sqrt P with hS
    have hSS : S * S = P := CFC.sqrt_mul_sqrt_self _ (ha := hP.nonneg)
    have hSh : Sᴴ = S := ((CFC.sqrt_nonneg P).posSemidef).isHermitian
    have hWW : Wᴴ * W = 1 := by
      rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hW
    have hXY : (S * Wᴴ)ᴴ * (S * V) = W * M := by
      rw [Matrix.conjTranspose_mul, hSh, Matrix.conjTranspose_conjTranspose, hMV,
        Matrix.mul_assoc, ← Matrix.mul_assoc S S V, hSS]
    have hXX : ((S * Wᴴ)ᴴ * (S * Wᴴ)).trace = P.trace := by
      rw [Matrix.conjTranspose_mul, hSh, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc, ← Matrix.mul_assoc S S Wᴴ, hSS, ← Matrix.mul_assoc,
        Matrix.trace_mul_cycle, hWW, Matrix.one_mul]
    have hYY : ((S * V)ᴴ * (S * V)).trace = P.trace := by
      rw [Matrix.conjTranspose_mul, hSh, Matrix.mul_assoc, ← Matrix.mul_assoc S S V, hSS,
        ← Matrix.mul_assoc, Matrix.trace_mul_cycle, hVV, Matrix.one_mul]
    calc ‖(W * M).trace‖ = ‖((S * Wᴴ)ᴴ * (S * V)).trace‖ := by rw [hXY]
      _ ≤ Real.sqrt (((S * Wᴴ)ᴴ * (S * Wᴴ)).trace.re) *
            Real.sqrt (((S * V)ᴴ * (S * V)).trace.re) :=
          norm_trace_conjTranspose_mul_le _ _
      _ = traceNorm M := by rw [hXX, hYY, htN]; exact Real.mul_self_sqrt htrre

/-! ### Fidelity -/

/-- The fidelity of two density matrices: `F(ρ, σ) = Tr √(√ρ σ √ρ)`. -/
