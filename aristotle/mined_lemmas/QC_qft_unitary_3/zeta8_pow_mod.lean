/-
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

open Complex Matrix

/-- The primitive `8`-th root of unity `ω = e^{2πi/8}` used by the 3-qubit QFT. -/

lemma zeta8_pow_mod (a : ℕ) : zeta8 ^ a = zeta8 ^ (a % 8) := by
  conv_lhs => rw [← Nat.div_add_mod a 8]
  rw [pow_add, pow_mul, zeta8_pow_eight, one_pow, one_mul]

/-- **The 3-qubit QFT matrix is unitary.** -/
