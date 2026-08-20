/-
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Matrix

namespace QC

/-! ## The quantum side: the GHZ state and its Pauli eigenvalue relations -/

/-- Index type for a three-qubit computational basis. -/
abbrev Idx := Fin 2 × Fin 2 × Fin 2

/-- The Pauli `X` observable. -/

noncomputable def tensor3 (A B C : Matrix (Fin 2) (Fin 2) ℂ) : Matrix Idx Idx ℂ :=
  fun i j => A i.1 j.1 * B i.2.1 j.2.1 * C i.2.2 j.2.2

/-- The three-qubit GHZ state `(|000⟩ - |111⟩)/√2`. -/
