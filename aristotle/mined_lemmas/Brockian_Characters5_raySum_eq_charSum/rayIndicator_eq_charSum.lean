/-
# Ray Sum Eq Char Sum
Category: Characters
Target: Brockian.Characters5.raySum_eq_charSum
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

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `e` of `ZMod 5` with values in `ℂ`, `e x = ω ^ x.val`. -/

lemma rayIndicator_eq_charSum (n : ℕ) (r : ZMod 5) :
    (if (n : ZMod 5) = r then (1 : ℂ) else 0)
      = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (a * ((n : ZMod 5) - r)) := by
  by_cases h : (n : ZMod 5) = r
  · rw [sum_char_eq_ite, if_pos h, if_pos (sub_eq_zero.mpr h)]; norm_num
  · rw [sum_char_eq_ite, if_neg h, if_neg (fun hc => h (sub_eq_zero.mp hc))]; simp

/-- Ray-count identity: the number of elements of `S` on ray `r` equals
`(1/5) ∑_{a} ∑_{n ∈ S} e (a * (n - r))`. -/
