/-
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
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

namespace Chem

open Finset Matrix

/-- `zeta a = exp (2πi a / 12)`, the `a`-th power of a primitive 12th root of unity. -/

lemma zeta_eq_zpow (a : ℤ) : zeta a = zeta 1 ^ a := by
  have h : (2 * Real.pi * Complex.I * (a : ℂ) / 12)
      = (a : ℂ) * (2 * Real.pi * Complex.I * ((1 : ℤ) : ℂ) / 12) := by
    push_cast; ring
  rw [zeta, h, Complex.exp_int_mul]
  rfl

