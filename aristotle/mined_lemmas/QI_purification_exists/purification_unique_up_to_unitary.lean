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

theorem purification_unique_up_to_unitary [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {ρ : Matrix n n ℂ} (ψ φ : n × m → ℂ) (hψ : IsPurification ρ ψ) (hφ : IsPurification ρ φ) :
    ∃ U : Matrix m m ℂ, U ∈ Matrix.unitaryGroup m ℂ ∧
      ∀ i j, φ (i, j) = ∑ k, ψ (i, k) * U k j := by
  rw [isPurification_iff] at hψ hφ
  obtain ⟨U, hUmem, hU⟩ := exists_unitary_mul_eq (hψ.trans hφ.symm)
  refine ⟨U, hUmem, fun i j => ?_⟩
  have := congrFun (congrFun hU i) j
  simpa [coeffMatrix, Matrix.mul_apply] using this

/-- **Uniqueness of purifications up to an isometry of the ancillas.** Any two purifications
of the same state `ρ`, the first with an ancilla no larger than the second, are related by an
isometry `V` (`V Vᴴ = 1`) acting on the ancilla alone. -/
