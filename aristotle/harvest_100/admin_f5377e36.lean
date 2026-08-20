import Mathlib

/-!
# Ray Indicator Eq Char Sum
Category: Characters
Target: Brockian.Characters5.rayIndicator_eq_charSum
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

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character of `ZMod 5` with values in `ℂ`. -/
noncomputable def e (a : ZMod 5) : ℂ := omega ^ a.val

lemma e_eq_stdAddChar (a : ZMod 5) : e a = ZMod.stdAddChar a := by
  have h : ((a.val : ℤ) : ZMod 5) = a := by
    simp [ZMod.natCast_val, ZMod.intCast_cast]
  have h2 := ZMod.stdAddChar_coe (N := 5) (a.val : ℤ)
  rw [h] at h2
  rw [e, h2, omega, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Orthogonality of the additive characters of `ZMod 5`. -/
lemma sum_e_mul (b : ZMod 5) :
    ∑ a : ZMod 5, e (b * a) = if b = 0 then 5 else 0 := by
  simp only [e_eq_stdAddChar]
  split_ifs with h
  · simp [h, Finset.card_univ, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar 5 h)

/-- The indicator of the ray `n ≡ r (mod 5)`. -/
noncomputable def rayIndicator (r : ZMod 5) (n : ℕ) : ℂ := if (n : ZMod 5) = r then 1 else 0

/-- Indicator decomposition: the ray indicator `𝟙[n ≡ r (mod 5)]` equals
`(1/5) Σ_{a : ZMod 5} e (a * (n - r))`. -/
theorem rayIndicator_eq_charSum (r : ZMod 5) (n : ℕ) :
    rayIndicator r n = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (a * ((n : ZMod 5) - r)) := by
  set b : ZMod 5 := (n : ZMod 5) - r with hb
  have hsum : ∑ a : ZMod 5, e (a * b) = ∑ a : ZMod 5, e (b * a) := by
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [mul_comm]
  rw [hsum, sum_e_mul, rayIndicator]
  have hiff : b = 0 ↔ (n : ZMod 5) = r := by rw [hb, sub_eq_zero]
  by_cases h : (n : ZMod 5) = r
  · rw [if_pos h, if_pos (hiff.mpr h)]
    norm_num
  · rw [if_neg h, if_neg (fun hc => h (hiff.mp hc))]
    norm_num

end Characters5
end Brockian

