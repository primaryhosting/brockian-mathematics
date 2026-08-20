/-
# Integrality Shadow
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.integrality_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Integrality Shadow
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.integrality_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Zeta23Redux.LinAlg

/-- Montgomery's integrality step: for every natural number `m`, `2 * m ≤ m ^ 2 + 1`.
This is the scalar shadow of `(m - 1) ^ 2 ≥ 0`, whose matrix analogue is Lemma 3.2. -/
theorem integrality_shadow (m : ℕ) : 2 * m ≤ m ^ 2 + 1 := by
  have hsq : (0 : ℤ) ≤ ((m : ℤ) - 1) ^ 2 := sq_nonneg _
  have h : (2 * m : ℤ) ≤ (m : ℤ) ^ 2 + 1 := by nlinarith
  exact_mod_cast h

/-- Equivalent integer form of the integrality shadow. -/
theorem integrality_shadow_int (m : ℕ) : (m : ℤ) ^ 2 ≥ 2 * m - 1 := by
  have h : ((2 * m : ℕ) : ℤ) ≤ ((m ^ 2 + 1 : ℕ) : ℤ) := Int.ofNat_le.mpr (integrality_shadow m)
  push_cast at h
  linarith

end Zeta23Redux.LinAlg

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

