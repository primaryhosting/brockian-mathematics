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

theorem syndrome_injective_wt_le_one {E₁ E₂ : PauliErr} (h₁ : wt E₁ ≤ 1) (h₂ : wt E₂ ≤ 1)
    (h : syndrome E₁ = syndrome E₂) : E₁ = E₂ := by
  obtain ⟨q₁, a₁, b₁, rfl⟩ := (wt_le_one_iff E₁).mp h₁
  obtain ⟨q₂, a₂, b₂, rfl⟩ := (wt_le_one_iff E₂).mp h₂
  exact syndrome_injective_on_single q₁ q₂ a₁ b₁ a₂ b₂ h

end Steane

open Steane in
/-- **The 7-qubit Steane (CSS) code corrects any single-qubit error.**

Formally: there is a recovery (decoding) map from measured stabilizer syndromes to Pauli
operators which returns exactly the error that occurred, for *every* Pauli error acting on at
most one of the seven qubits.  Equivalently, the stabilizer syndrome separates all
weight-`≤ 1` Pauli errors, which is the Knill–Laflamme error-correction condition for a
stabilizer code of distance 3. -/
