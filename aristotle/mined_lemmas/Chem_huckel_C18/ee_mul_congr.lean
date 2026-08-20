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

set_option grind.warning false

namespace Chem

open Complex Polynomial Matrix

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/

lemma ee_mul_congr {a b c : ℕ} (h : a % 18 = b % 18) : ee ((a : ℤ) * c) = ee ((b : ℤ) * c) := by
  apply ee_congr
  have h18 : (18 : ℤ) ∣ (a : ℤ) - b := by omega
  obtain ⟨t, ht⟩ := h18
  exact ⟨t * c, by linear_combination (c : ℤ) * ht⟩

