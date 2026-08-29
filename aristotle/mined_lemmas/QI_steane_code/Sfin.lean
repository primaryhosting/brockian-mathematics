/-
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the
-- header above is a plain block comment; it is repeated verbatim as the module
-- docstring immediately after the import.)

import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## The classical ingredients: the `[7,4,3]` Hamming code and its dual -/

/-- A binary register of 7 bits.  Also used to index the computational basis of the
7-qubit Hilbert space. -/
abbrev Reg := Fin 7 → ZMod 2

/-- The `𝔽₂`-bilinear form used both for parity checks and for Pauli phases. -/

def Sfin : Finset Reg := {0, r1, r2, r1+r2, r3, r1+r3, r2+r3, r1+r2+r3}

/-! ### Structural sanity checks on the two classical codes -/

/-- `Sfin` is exactly the row space of the parity check matrix, i.e. the dual code. -/
