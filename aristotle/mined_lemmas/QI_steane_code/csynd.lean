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

import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxRecDepth 100000

namespace QI

namespace Steane

/-! ## The classical `[7,4,3]` Hamming code

`steaneH i j` is the `(i,j)` entry of the parity-check matrix of the Hamming code:
the `i`-th binary digit of the column index `j + 1`.  Explicitly the matrix is

```
1 0 1 0 1 0 1
0 1 1 0 0 1 1
0 0 0 1 1 1 1
```
-/

/-- Parity-check matrix of the classical `[7,4,3]` Hamming code, over `GF(2) = ZMod 2`. -/

def csynd (e : Fin 7 → ZMod 2) : Fin 3 → ZMod 2 := steaneH.mulVec e

/-! ## Pauli errors on 7 qubits

A Pauli error (up to phase) on `n` qubits is described by its symplectic representation
`(x, z) ∈ (GF(2)^n)²`: qubit `j` carries `X^(x j) Z^(z j)`. -/

/-- A Pauli error on the 7 qubits, in symplectic (`X`-part, `Z`-part) representation. -/
abbrev PauliErr : Type := (Fin 7 → ZMod 2) × (Fin 7 → ZMod 2)

/-- The pair of syndromes measured by the Steane code stabilizers: the `X`-type stabilizers
(given by `steaneH`) detect the `Z`-part of the error, and the `Z`-type stabilizers (also
given by `steaneH`, this is a CSS code) detect the `X`-part. -/
