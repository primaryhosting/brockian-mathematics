import Mathlib

/-!
# Ray Indicator Eq Char Sum
Category: Characters
Target: Brockian.Characters5.rayIndicator_eq_charSum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `e : ZMod 5 → ℂ`, `e a = ω ^ a`. -/
noncomputable def e (a : ZMod 5) : ℂ := omega ^ a.val

theorem omega_isPrimitiveRoot : IsPrimitiveRoot omega 5 := by
  simpa [omega] using Complex.isPrimitiveRoot_exp 5 (by norm_num)

theorem e_zero : e 0 = 1 := by
  simp [e]

/-- The sum of `e` over all of `ZMod 5` vanishes. -/
theorem sum_e : ∑ a : ZMod 5, e a = 0 := by
  have h : ∑ i ∈ Finset.range 5, omega ^ i = 0 :=
    omega_isPrimitiveRoot.geom_sum_eq_zero (by norm_num)
  rw [← h, show (∑ a : ZMod 5, e a) = ∑ a : Fin 5, omega ^ (a : ℕ) from rfl]
  simp [Fin.sum_univ_five, Finset.sum_range_succ]

/-- Orthogonality relation for the character `e`. -/
theorem sum_e_mul (b : ZMod 5) :
    ∑ a : ZMod 5, e (b * a) = if b = 0 then 5 else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hb : b = 0
  · subst hb
    simp [e_zero]
  · rw [if_neg hb, ← sum_e]
    exact Equiv.sum_comp (Equiv.mulLeft₀ b hb) e

/-- Indicator of the ray `n ≡ r (mod 5)`. -/
noncomputable def rayIndicator (r : ZMod 5) (n : ℕ) : ℂ := if (n : ZMod 5) = r then 1 else 0

/-- Spectral decomposition of the ray indicator as a character sum. -/
theorem rayIndicator_eq_charSum (r : ZMod 5) (n : ℕ) :
    rayIndicator r n = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (a * ((n : ZMod 5) - r)) := by
  set b : ZMod 5 := (n : ZMod 5) - r with hbdef
  have hsum : ∑ a : ZMod 5, e (a * b) = if b = 0 then 5 else 0 := by
    rw [← sum_e_mul b]
    exact Finset.sum_congr rfl fun a _ => by rw [mul_comm]
  rw [hsum, rayIndicator]
  by_cases h : (n : ZMod 5) = r
  · rw [if_pos h, if_pos (by rw [hbdef, h, sub_self])]
    norm_num
  · rw [if_neg h, if_neg (by rw [hbdef, sub_eq_zero]; exact h)]
    norm_num

end Characters5
end Brockian

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

