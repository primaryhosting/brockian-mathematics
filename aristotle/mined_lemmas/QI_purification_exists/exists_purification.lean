import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Statement: Every mixed state has a purification, unique up to isometry on the ancilla.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QI

/-!
## Setting

A state of a finite dimensional quantum system with basis indexed by `n` is a positive
semidefinite matrix `ρ : Matrix n n ℂ` of trace one.

A vector of the composite system `H ⊗ K`, where `K` is an ancilla with basis indexed by `m`,
is encoded by its matrix of coefficients `A : Matrix n m ℂ`, i.e. `A` encodes
`∑ i, ∑ j, A i j • (e i ⊗ f j)`.  With this encoding the reduced density matrix
(the partial trace over the ancilla) of the pure state `|A⟩⟨A|` is exactly `A * Aᴴ`, and the
squared norm of the vector is `∑ i, ∑ j, ‖A i j‖ ^ 2 = trace (A * Aᴴ)`.

Consequently `A` purifies `ρ` exactly when `A * Aᴴ = ρ`, and an isometry `K → K'` of ancillas
acting on the second tensor factor sends the vector `A` to `A * W`, where `W : Matrix m m' ℂ`
satisfies `W * Wᴴ = 1`.
-/

/-- `A` is a purification of the state `ρ`: the reduced density matrix (partial trace over the
ancilla) of the pure state given by the vector with coefficient matrix `A` equals `ρ`. -/

theorem exists_purification {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) : IsPurification ρ (CFC.sqrt ρ) := by
  have hherm : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ := (CFC.sqrt_nonneg ρ).posSemidef.isHermitian
  rw [IsPurification, hherm]
  exact CFC.sqrt_mul_sqrt_self ρ (by exact hρ.nonneg)

/-- A purification of a state of trace one is a unit vector. -/
