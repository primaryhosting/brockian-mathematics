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

lemma ee_congr {a b : ℤ} (h : (18 : ℤ) ∣ a - b) : ee a = ee b := by
  obtain ⟨t, ht⟩ := h
  have hab : a = b + 18 * t := by omega
  rw [hab, ee, zpow_add₀ zeta_ne_zero, _root_.zpow_mul,
    show ((zeta : ℂ) ^ (18 : ℤ)) = 1 by exact_mod_cast zeta_primitive.pow_eq_one]
  simp [ee]

