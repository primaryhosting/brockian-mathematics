import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QI

section Defs

variable {n m : Type*}

/-- The density matrix `|ψ⟩⟨ψ|` of a state vector `ψ` of a composite system whose
product basis is indexed by `n × m`. -/

theorem exists_purification [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    ∃ ψ : n × n → ℂ, IsPurification ρ ψ ∧ ∑ p, ‖ψ p‖ ^ 2 = 1 := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hρ.nonneg
  set A : Matrix n n ℂ := Bᴴ with hA
  have hAA : A * Aᴴ = ρ := by simpa [hA, Matrix.star_eq_conjTranspose] using hB.symm
  refine ⟨fun p => A p.1 p.2, ?_, ?_⟩
  · rw [isPurification_iff]
    have : coeffMatrix (fun p : n × n => A p.1 p.2) = A := rfl
    rw [this, hAA]
  · have htrace : ((∑ p : n × n, ‖A p.1 p.2‖ ^ 2 : ℝ) : ℂ) = ρ.trace := by
      rw [← hAA]
      rw [Matrix.trace]
      push_cast
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.diag_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.conjTranspose_apply, RCLike.star_def, Complex.mul_conj]
      simp [Complex.normSq_eq_norm_sq]
    rw [htr] at htrace
    exact_mod_cast htrace

/-- **Uniqueness of purifications up to a unitary on the ancilla.** Any two purifications of
the same state `ρ`, using the same ancilla, are related by a unitary acting on the ancilla
alone. -/
