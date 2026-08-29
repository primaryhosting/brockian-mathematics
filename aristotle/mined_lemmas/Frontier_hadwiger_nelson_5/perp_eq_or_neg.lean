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

import Mathlib

/-!
# Basic notions for the Hadwiger–Nelson problem

We identify the Euclidean plane with `ℂ`.  A *proper* 4-colouring is a map
`c : ℂ → Fin 4` such that no two points at distance exactly `1` receive the
same colour.  We phrase the distance condition with `Complex.normSq` (the
squared modulus) so that all verifications stay polynomial.
-/

namespace CNP

open Complex

/-- A proper 4-colouring of the plane. -/

theorem perp_eq_or_neg {a1 a2 b1 b2 d1 d2 : ℝ}
    (ha : a1 * d1 + a2 * d2 = 0) (hb : b1 * d1 + b2 * d2 = 0)
    (hn : a1 ^ 2 + a2 ^ 2 = b1 ^ 2 + b2 ^ 2) (hd : d1 ^ 2 + d2 ^ 2 ≠ 0) :
    (a1 = b1 ∧ a2 = b2) ∨ (a1 = -b1 ∧ a2 = -b2) := by
  have hdet : a1 * b2 - a2 * b1 = 0 := by
    rcases eq_or_ne d1 0 with h1 | h1
    · have h2 : d2 ≠ 0 := fun h2 => hd (by rw [h1, h2]; ring)
      have ea : a2 * d2 = 0 := by rw [h1] at ha; linarith
      have eb : b2 * d2 = 0 := by rw [h1] at hb; linarith
      have hz : d2 * (a1 * b2 - a2 * b1) = 0 := by linear_combination a1 * eb - b1 * ea
      rcases mul_eq_zero.1 hz with h | h
      · exact absurd h h2
      · exact h
    · have hz : d1 * (a1 * b2 - a2 * b1) = 0 := by linear_combination b2 * ha - a2 * hb
      rcases mul_eq_zero.1 hz with h | h
      · exact absurd h h1
      · exact h
  have key : ((a1 - b1) ^ 2 + (a2 - b2) ^ 2) * ((a1 + b1) ^ 2 + (a2 + b2) ^ 2) = 0 := by
    linear_combination ((a1 ^ 2 + a2 ^ 2) - (b1 ^ 2 + b2 ^ 2)) * hn +
      (4 * (a1 * b2 - a2 * b1)) * hdet
  rcases mul_eq_zero.1 key with h | h
  · left
    have h1 : (a1 - b1) ^ 2 = 0 := by nlinarith [sq_nonneg (a1 - b1), sq_nonneg (a2 - b2)]
    have h2 : (a2 - b2) ^ 2 = 0 := by nlinarith [sq_nonneg (a1 - b1), sq_nonneg (a2 - b2)]
    constructor
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1; linarith
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2; linarith
  · right
    have h1 : (a1 + b1) ^ 2 = 0 := by nlinarith [sq_nonneg (a1 + b1), sq_nonneg (a2 + b2)]
    have h2 : (a2 + b2) ^ 2 = 0 := by nlinarith [sq_nonneg (a1 + b1), sq_nonneg (a2 + b2)]
    constructor
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1; linarith
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2; linarith

/-- Given a segment `p q` of squared length 3, there are at most two points at squared
distance 3 from both endpoints, and they are reflections of one another. -/
