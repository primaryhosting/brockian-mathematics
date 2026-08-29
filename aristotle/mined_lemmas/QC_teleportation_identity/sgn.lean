/-
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QC

open Complex Finset

/-- The scalar `1/√2`, the normalization constant of the Bell states. -/

def sgn (a i : Bool) : ℂ := if a && i then -1 else 1

/-- The four Bell states `B a b`, indexed by two classical bits `a` (phase) and `b` (parity):
`B a b i j = (-1)^(a·i)/√2` if `j = i ⊕ b`, and `0` otherwise.
Thus `B false false = (|00⟩+|11⟩)/√2`, `B false true = (|01⟩+|10⟩)/√2`,
`B true false = (|00⟩-|11⟩)/√2`, `B true true = (|01⟩-|10⟩)/√2`. -/
