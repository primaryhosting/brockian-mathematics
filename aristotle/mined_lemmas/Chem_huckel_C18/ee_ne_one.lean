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

lemma ee_ne_one {d : ℤ} (h : ¬ (18 : ℤ) ∣ d) : ee d ≠ 1 := by
  intro hc
  refine h ?_
  have hd := zeta_primitive.zpow_eq_one_iff_dvd d
  simp only [ee] at hc
  exact_mod_cast hd.mp hc

