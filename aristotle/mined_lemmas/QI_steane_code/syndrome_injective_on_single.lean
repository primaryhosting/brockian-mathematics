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

theorem syndrome_injective_on_single (q₁ q₂ : Fin 7) (a₁ b₁ a₂ b₂ : ZMod 2)
    (h : syndrome (single q₁ a₁ b₁) = syndrome (single q₂ a₂ b₂)) :
    single q₁ a₁ b₁ = single q₂ a₂ b₂ := by
  revert h
  revert q₁ q₂ a₁ b₁ a₂ b₂
  decide

/-- The syndrome map is injective on the set of Pauli errors of weight at most one. -/
