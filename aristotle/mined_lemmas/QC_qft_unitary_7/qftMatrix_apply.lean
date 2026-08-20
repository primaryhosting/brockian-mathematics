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

lemma qftMatrix_apply (N : ℕ) [NeZero N] (j k : ZMod N) :
    qftMatrix N j k = (Real.sqrt N : ℂ)⁻¹ * ZMod.stdAddChar (j * k) := by
  have h : ((j.val * k.val : ℤ) : ZMod N) = j * k := by
    push_cast [ZMod.natCast_val, ZMod.cast_id]; ring
  rw [qftMatrix, ← h, ZMod.stdAddChar_coe]
  push_cast
  ring_nf

/-- The standard additive character takes values on the unit circle, so complex conjugation
inverts it. -/
