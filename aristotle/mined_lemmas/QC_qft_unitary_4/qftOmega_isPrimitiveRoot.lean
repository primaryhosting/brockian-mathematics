import Mathlib
/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
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

open Complex Finset Matrix

/-- The primitive `n`-th root of unity `exp (2πi/n)` used by the quantum Fourier transform. -/

lemma qftOmega_isPrimitiveRoot (n : ℕ) (hn : n ≠ 0) :
    IsPrimitiveRoot (qftOmega n) n :=
  Complex.isPrimitiveRoot_exp n hn

