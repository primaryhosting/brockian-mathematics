import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Statement: The 7-qubit Steane (CSS) code corrects any single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Classical setup: the Hamming `[7,4,3]` code and its dual -/

/-- Bit strings of length 7 (the computational basis labels of 7 qubits). -/
abbrev Bits := Fin 7 → ZMod 2

/-- The parity check matrix of the classical Hamming `[7,4,3]` code. -/

def lvec (l : ZMod 2) : Bits := if l = 0 then 0 else ones

/-- The two logical basis states of the Steane code: `psi 0 = ∑_{c ∈ C₂} |c⟩` and
`psi 1 = ∑_{c ∈ C₂} |c + 1111111⟩` (unnormalised). -/
