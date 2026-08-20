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

def ghz : Idx → ℂ := fun p => if p = (0, 0, 0) then 1 else if p = (1, 1, 1) then 1 else 0

