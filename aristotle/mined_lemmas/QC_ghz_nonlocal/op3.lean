/-
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Matrix Complex
open scoped Kronecker

/-- The Pauli `X` matrix. -/

def op3 (A B C : Matrix (Fin 2) (Fin 2) ℂ) : Matrix Idx Idx ℂ := A ⊗ₖ (B ⊗ₖ C)

/-- The (unnormalised) GHZ state `|000⟩ + |111⟩`. -/
