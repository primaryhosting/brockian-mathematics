/-
# Ghz 8 Normalized
Category: Quantum Computing
Target: QC.ghz8_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is kept as a plain block comment because Lean 4 does not
-- allow a module docstring `/-! ... -/` to precede the `import` command.)

import Mathlib

namespace QC

/-- The 8-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`, described as a vector in the
Hilbert space `ℂ^(Fin 8 → Bool)` of 8 qubits: its amplitude is `1/√2` on the two
computational basis states `|00000000⟩` and `|11111111⟩`, and `0` elsewhere. -/

theorem ghz8_inner_self : inner ℂ ghz8 ghz8 = (1 : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K, ghz8_normalized]
  norm_num

end QC

#print axioms QC.ghz8_normalized
#print axioms QC.ghz8_eq
#print axioms QC.ghz8_inner_self

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

