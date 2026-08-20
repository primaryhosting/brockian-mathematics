/-
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
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

set_option grind.warning false

namespace QC

open Complex Finset

/-- The `N × N` quantum Fourier transform matrix, with rows and columns indexed by `ZMod N`:
its `(j, k)` entry is `N ^ (-1/2) * exp (2 π i j k / N)`.  For `N = 2 ^ n` this is the QFT on
`n` qubits (with computational basis states identified with residues mod `2 ^ n`). -/

lemma conj_stdAddChar (N : ℕ) [NeZero N] (x : ZMod N) :
    (starRingEnd ℂ) (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv,
    ← Circle.coe_inv_eq_conj]

/-- Orthogonality relation: the character sum `∑ k, e (t k / N)` is `N` if `t = 0` and `0`
otherwise. -/
