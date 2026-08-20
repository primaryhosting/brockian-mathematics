/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
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

namespace Chem

open Complex Matrix

/-- The primitive 14-th root of unity `exp(2πi/14)`. -/

lemma om_zpow_eq {a b : ℤ} (h : (14 : ℤ) ∣ a - b) : om ^ a = om ^ b := by
  obtain ⟨c, hc⟩ := h
  have ha : a = b + 14 * c := by linarith
  have h14 : om ^ (14 : ℤ) = 1 := by
    rw [show (14 : ℤ) = ((14 : ℕ) : ℤ) by norm_num, zpow_natCast, om_pow14]
  rw [ha, zpow_add₀ om_ne_zero, _root_.zpow_mul, h14, _root_.one_zpow, mul_one]

/-- The Hückel eigenvalue `2 cos (2πk/14)` as a sum of two powers of `om`. -/
