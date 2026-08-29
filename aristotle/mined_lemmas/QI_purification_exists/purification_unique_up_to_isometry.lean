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

theorem purification_unique_up_to_isometry {m' : Type*} [Fintype n] [Fintype m] [Fintype m']
    [DecidableEq n] [DecidableEq m] [DecidableEq m'] {ρ : Matrix n n ℂ}
    (ψ : n × m → ℂ) (φ : n × m' → ℂ) (hψ : IsPurification ρ ψ) (hφ : IsPurification ρ φ)
    (hcard : Fintype.card m ≤ Fintype.card m') :
    ∃ V : Matrix m m' ℂ, V * Vᴴ = 1 ∧ ∀ i j, φ (i, j) = ∑ k, ψ (i, k) * V k j := by
  rw [isPurification_iff] at hψ hφ
  obtain ⟨V, hViso, hV⟩ := exists_isometry_mul_eq (hψ.trans hφ.symm) hcard
  refine ⟨V, hViso, fun i j => ?_⟩
  have := congrFun (congrFun hV i) j
  simpa [coeffMatrix, Matrix.mul_apply] using this

/-- **Purification exists, and is unique up to an isometry (indeed a unitary) on the
ancilla.** Every mixed state `ρ` on `H_A` — a positive semidefinite matrix of trace one —
admits a purification: a unit vector `ψ` of `H_A ⊗ H_B` whose reduced density matrix,
obtained by tracing out the ancilla, is `ρ`. Moreover any two purifications of `ρ` with the
same ancilla are related by a unitary acting on the ancilla only. -/
