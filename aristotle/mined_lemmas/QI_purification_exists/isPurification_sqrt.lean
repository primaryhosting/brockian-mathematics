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

theorem isPurification_sqrt {ρ : Matrix H H ℂ} (hpsd : ρ.PosSemidef) :
    IsPurification ρ (fun p : H × H => CFC.sqrt ρ p.1 p.2) := by
  have hsq : (CFC.sqrt ρ).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)
  have hmul : CFC.sqrt ρ * CFC.sqrt ρ = ρ :=
    CFC.sqrt_mul_sqrt_self ρ (Matrix.nonneg_iff_posSemidef.mpr hpsd)
  show reducedState _ = ρ
  ext i j
  have hij : (CFC.sqrt ρ * (CFC.sqrt ρ)ᴴ) i j = ρ i j := by rw [hsq.isHermitian.eq, hmul]
  simpa [reducedState, Matrix.mul_apply, Matrix.conjTranspose_apply] using hij

/-- **Purification exists and is unique up to an isometry of the ancilla.**

For every mixed state `ρ` (a positive semidefinite matrix of unit trace) on a finite dimensional
system `H`:

* there is a pure state `ψ` of `H ⊗ H` (a unit vector, as recorded by the second conjunct)
  whose reduced state on `H` — the partial trace over the ancilla — is `ρ`;
* any two purifications `ψ`, `φ` of `ρ` sharing the same ancilla `K` are related by a
  unitary (hence isometric) transformation `U` acting on the ancilla alone. -/
