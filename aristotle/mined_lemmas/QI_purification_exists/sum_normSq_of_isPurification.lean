import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped ComplexConjugate MatrixOrder ComplexOrder

namespace QI

/-! ### Basic definitions -/

section Defs

variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- A density matrix (mixed state): a positive semidefinite matrix of unit trace. -/

theorem sum_normSq_of_isPurification {K : Type*} [Fintype K] [DecidableEq K]
    {ρ : Matrix H H ℂ} (hρ : ρ.trace = 1) {ψ : H × K → ℂ} (hψ : IsPurification ρ ψ) :
    ∑ p : H × K, ‖ψ p‖ ^ 2 = 1 := by
  have hz : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
    intro z
    rw [Complex.mul_conj']
    push_cast
    ring
  have h1 : ((∑ p : H × K, ‖ψ p‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← hρ, ← hψ]
    simp only [Matrix.trace, Matrix.diag, reducedState, Matrix.of_apply, Complex.ofReal_sum,
      Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hz _
  exact_mod_cast h1

/-- The positive square root of a mixed state `ρ`, read as a vector of `H ⊗ H`, purifies `ρ`. -/
