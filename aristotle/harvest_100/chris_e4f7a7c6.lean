/-
# Psi Cubic Le One
Category: A Assembly
Target: Zeta23Scaffold.psiCubic_le_one
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Scaffold

/-- The cubic weight `psi`. -/
def psiCubic (m : Nat) : Rat :=
  (m : Rat) / 2 + (2 * (m : Rat) ^ 2 - (m : Rat) ^ 3) / 18 + (if m = 1 then 4 / 9 else 0)

/-- Key identity: for `m ≥ 2` the indicator vanishes and
`18 * (1 - psiCubic m) = (m - 2) * (m - 3) * (m + 3)`. -/
lemma eighteen_mul_one_sub_psiCubic {m : Nat} (hm : 2 ≤ m) :
    18 * (1 - psiCubic m) = ((m : Rat) - 2) * ((m : Rat) - 3) * ((m : Rat) + 3) := by
  have hm1 : m ≠ 1 := by omega
  simp only [psiCubic, hm1, if_false, add_zero]
  ring

/-- The product `(m - 2) * (m - 3)` is nonnegative for every natural `m`. -/
lemma mul_sub_nonneg (m : Nat) : 0 ≤ ((m : Rat) - 2) * ((m : Rat) - 3) := by
  rcases lt_or_ge m 3 with h | h
  · have h2 : (m : Rat) ≤ 2 := by
      have : m ≤ 2 := by omega
      exact_mod_cast this
    have h3 : (m : Rat) ≤ 3 := by linarith
    nlinarith
  · have h3 : (3 : Rat) ≤ (m : Rat) := by exact_mod_cast h
    nlinarith

/-- `psiCubic m ≤ 1` for all integers `m ≥ 1`. -/
theorem psiCubic_le_one : ∀ m : Nat, 1 ≤ m → psiCubic m ≤ 1 := by
  intro m hm
  rcases eq_or_lt_of_le hm with h | h
  · subst_vars
    norm_num [psiCubic]
  · have hm2 : 2 ≤ m := h
    have hid := eighteen_mul_one_sub_psiCubic hm2
    have hpos : (0 : Rat) ≤ (m : Rat) + 3 := by positivity
    have hprod : 0 ≤ ((m : Rat) - 2) * ((m : Rat) - 3) := mul_sub_nonneg m
    nlinarith [mul_nonneg hprod hpos]

end Zeta23Scaffold

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

