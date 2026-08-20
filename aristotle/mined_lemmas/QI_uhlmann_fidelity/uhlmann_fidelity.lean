/-
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file proves **Uhlmann's theorem**: for positive semidefinite states `ρ`, `σ` on `ℂ^n`,
the fidelity `F(ρ, σ) = Tr √(√ρ σ √ρ)` is the *maximal* overlap `|⟪ψ, φ⟫|` taken over all
purifications `ψ` of `ρ` and `φ` of `σ` in `ℂ^n ⊗ ℂ^n`, where a purification of `ρ` is a
vector whose reduced density matrix (partial trace over the second factor) is `ρ`.

Neither quantum fidelity nor purifications (nor even the polar decomposition of a matrix)
are available in Mathlib, so everything is developed here from scratch:

* `QI.abs_trace_conjTranspose_mul_le`: Cauchy–Schwarz/AM–GM for the Hilbert–Schmidt
  inner product, `|Tr (Aᴴ B)| ≤ (‖A‖₂² + ‖B‖₂²) / 2`.
* `QI.exists_unitary_polar`: the polar decomposition `M = √(M Mᴴ) U` with `U` unitary,
  obtained by extending the isometry `√(M Mᴴ) x ↦ Mᴴ x` to a unitary of `ℂ^n`.
* `QI.norm_trace_mul_unitary_le`: `|Tr (Q Y)| ≤ Tr Q` for `Q ≥ 0` and `Y` unitary.
* `QI.uhlmann_fidelity_matrix` and `QI.uhlmann_fidelity`: Uhlmann's theorem, in matrix
  form and in terms of purifying vectors.
-/

open scoped MatrixOrder ComplexOrder BigOperators
open Matrix

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The Hilbert–Schmidt (Frobenius) inner product -/

/-- The squared Frobenius (Hilbert–Schmidt) norm of a matrix. -/

theorem uhlmann_fidelity (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    IsGreatest {r : ℝ | ∃ ψ φ : n × n → ℂ,
      ptrace ψ = ρ ∧ ptrace φ = σ ∧ r = ‖∑ p, star (ψ p) * φ p‖} (fidelity ρ σ) := by
  constructor
  · obtain ⟨A, B, hA, hB, hval⟩ := exists_overlap_eq_fidelity hρ hσ
    refine ⟨fun p => A p.1 p.2, fun p => B p.1 p.2, ?_, ?_, ?_⟩
    · rw [ptrace_eq_mul_conjTranspose]
      exact hA
    · rw [ptrace_eq_mul_conjTranspose]
      exact hB
    · rw [overlap_eq_trace]
      exact hval
  · rintro r ⟨ψ, φ, hψ, hφ, rfl⟩
    rw [overlap_eq_trace]
    refine overlap_le_fidelity hρ hσ (toMat ψ) (toMat φ) ?_ ?_
    · rw [← ptrace_eq_mul_conjTranspose]; exact hψ
    · rw [← ptrace_eq_mul_conjTranspose]; exact hφ

end Main

end QI

import Mathlib

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

