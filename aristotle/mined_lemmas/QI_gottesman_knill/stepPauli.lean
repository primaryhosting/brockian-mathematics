/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-! ## Bit strings and phases -/

/-- The computational basis of `n` qubits is indexed by bit strings `Fin n → ZMod 2`. -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- The `𝔽₂`-valued inner product of two bit strings. -/

def stepPauli {n : ℕ} : Gate n → Pauli n → Pauli n
  | .H i, P => ⟨P.ph + dbl (P.xs i * P.zs i),
      Function.update P.xs i (P.zs i), Function.update P.zs i (P.xs i)⟩
  | .S i, P => ⟨P.ph + (if P.xs i = 0 then 0 else 3),
      P.xs, Function.update P.zs i (P.zs i + P.xs i)⟩
  | .CX i j _, P => ⟨P.ph,
      Function.update P.xs j (P.xs j + P.xs i), Function.update P.zs i (P.zs i + P.zs j)⟩

/-- The unitary of a stabilizer circuit, given as a list of gates in time order. -/
