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

lemma zeta_periodic {a b : ℤ} (h : a % 12 = b % 12) : zeta a = zeta b := by
  obtain ⟨n, rfl⟩ : ∃ n, a = b + 12 * n := ⟨(a - b) / 12, by omega⟩
  rw [zeta_add, zeta_eq_zpow (12 * n), _root_.zpow_mul, zeta_one_pow_twelve, _root_.one_zpow, mul_one]

