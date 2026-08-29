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

noncomputable def ancillaAct (U : Matrix K K ℂ) (ψ : H × K → ℂ) : H × K → ℂ :=
  fun p => ∑ l, U p.2 l * ψ (p.1, l)

/-- The matrix whose `(i, k)` entry is the amplitude `ψ (i, k)`. -/
