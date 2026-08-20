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

def stabZ (r : Fin 3) : Pauli := ⟨0, fun i => hcol i r⟩

/-- The three `X`-type stabilizer generators of the Steane code, given by the rows of the
Hamming parity-check matrix. -/
