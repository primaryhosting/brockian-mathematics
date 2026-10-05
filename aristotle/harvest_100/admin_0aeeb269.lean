/-
# Psi Cubic Le One
Category: A Assembly
Target: Zeta23Scaffold.psiCubic_le_one
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Zeta23Scaffold

/-- The cubic weight `ψ`. -/
def psiCubic (m : ℕ) : ℚ :=
  (m : ℚ) / 2 + (2 * (m : ℚ) ^ 2 - (m : ℚ) ^ 3) / 18 + (if m = 1 then 4 / 9 else 0)

/-- For `m ≥ 2` the factorization `18 * (1 - ψ(m)) = (m-2)(m-3)(m+3)` holds. -/
theorem eighteen_mul_one_sub_psiCubic (m : ℕ) (hm : 2 ≤ m) :
    18 * (1 - psiCubic m) = ((m : ℚ) - 2) * ((m : ℚ) - 3) * ((m : ℚ) + 3) := by
  have h : m ≠ 1 := by omega
  simp only [psiCubic, h, if_false]
  ring

/-- For an integer `m ≥ 2`, `(m-2)(m-3) ≥ 0`. -/
theorem nonneg_mul_sub_two_sub_three (m : ℕ) (hm : 2 ≤ m) :
    (0 : ℚ) ≤ ((m : ℚ) - 2) * ((m : ℚ) - 3) := by
  rcases (by omega : m = 2 ∨ m = 3 ∨ 4 ≤ m) with h | h | h
  · subst h; norm_num
  · subst h; norm_num
  · have : (4 : ℚ) ≤ (m : ℚ) := by exact_mod_cast h
    nlinarith

/-- `ψ(m) ≤ 1` for every integer `m ≥ 1`. -/
theorem psiCubic_le_one (m : ℕ) (hm : 1 ≤ m) : psiCubic m ≤ 1 := by
  rcases (by omega : m = 1 ∨ 2 ≤ m) with h | hm2
  · subst h; norm_num [psiCubic]
  · have hfac := eighteen_mul_one_sub_psiCubic m hm2
    have hnn := nonneg_mul_sub_two_sub_three m hm2
    have hpos : (0 : ℚ) < (m : ℚ) + 3 := by positivity
    nlinarith [mul_nonneg hnn (le_of_lt hpos)]

end Zeta23Scaffold

