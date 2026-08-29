/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
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

open Complex Matrix

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

lemma qftOmega_pow_eq_one_iff (n : ℕ) (hn : n ≠ 0) (m : ℕ) :
    qftOmega n ^ m = 1 ↔ n ∣ m :=
  (Complex.isPrimitiveRoot_exp n hn).pow_eq_one_iff_dvd m

/-- Orthogonality relation for the roots of unity. -/
