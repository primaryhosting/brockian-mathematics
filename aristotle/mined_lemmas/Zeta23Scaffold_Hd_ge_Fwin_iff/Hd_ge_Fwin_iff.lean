/-!
# Hd Ge Fwin Iff
Category: A Assembly
Target: Zeta23Scaffold.Hd_ge_Fwin_iff
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Zeta23Scaffold

/-- The "window" function `H(λ) = 2 - 1/λ - λ/3`. -/

theorem Hd_ge_Fwin_iff (lam : ℝ) (hpos : 0 < lam) (hle : lam ≤ 1) :
    Fwin lam ≤ Hd lam ↔ 0 ≤ Hwin lam := by
  have hden : 0 < 6 * lam * (3 + lam ^ 2) := by positivity
  have hq := aux_quadratic_pos lam
  rw [← sub_nonneg, Hd_sub_Fwin_eq hpos, Hwin_nonneg_iff hpos,
    div_nonneg_iff]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · nlinarith
    · nlinarith
  · intro h
    exact Or.inl ⟨by nlinarith, le_of_lt hden⟩

end Zeta23Scaffold

