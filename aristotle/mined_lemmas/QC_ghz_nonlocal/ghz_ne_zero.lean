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

theorem ghz_ne_zero : ghz ≠ 0 := by
  intro h
  have := congrFun h (0, 0, 0)
  simp [ghz] at this

