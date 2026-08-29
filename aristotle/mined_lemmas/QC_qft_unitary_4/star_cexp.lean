-- /-!
-- # Qft Unitary 4
-- Category: Quantum Computing
-- Target: QC.qft_unitary_4
-- Verification: pending
-- Provenance: Aristotle theorem prover (Harmonic)
-- -/

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

open scoped Matrix

namespace QC

/-- The `N`-point discrete (quantum) Fourier transform matrix:
`(qftMatrix N) j k = N^(-1/2) * exp (2πi·jk/N)`. -/

private lemma star_cexp (x : ℂ) : star (Complex.exp x) = Complex.exp (star x) := by
  simp [Complex.exp_conj]

/-- The `N`-th root of unity `exp (2πi·d/N)` differs from `1` when `N ∤ d`. -/
