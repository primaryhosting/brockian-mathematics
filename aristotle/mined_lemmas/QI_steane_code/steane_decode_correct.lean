import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` only because Lean 4 requires every
-- `import` to precede any module docstring; the text is otherwise verbatim.)

import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

/-! ## The binary field and the Hamming parity-check matrix -/

/-- The two-element field `GF(2)`. -/
abbrev F2 := ZMod 2

/-- Column `i` of the parity-check matrix of the `[7,4,3]` Hamming code: the binary
expansion of `i + 1`.  The seven columns are exactly the seven nonzero vectors of
`GF(2)³`, which is what makes the code single-error correcting. -/

theorem steane_decode_correct (E : Pauli) (hE : E.SingleQubit) : decode (syndrome E) = E := by
  obtain ⟨i, hi⟩ := (singleQubit_iff E).1 hE
  rw [hi]
  exact decode_ind i (E.x i) (E.z i)

/-- **The 7-qubit Steane code corrects any single-qubit error.**

Two single-qubit Pauli errors that produce the same syndrome (the same commutation
pattern with the six CSS stabilizer generators of the code) are equal; equivalently, the
explicit decoder `decode` recovers the error exactly from its syndrome
(`steane_decode_correct`).  This is the Knill–Laflamme correctability condition for the
stabilizer code: distinct correctable errors are distinguished by the measured syndrome,
so a recovery operation exists. -/
