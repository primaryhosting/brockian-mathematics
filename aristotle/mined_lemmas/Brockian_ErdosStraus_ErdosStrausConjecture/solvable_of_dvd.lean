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

/-
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.ErdosStraus

/-- `ErdosStrausSolvable n` says that `4 / n` is a sum of three unit fractions with
positive natural denominators. -/

theorem solvable_of_dvd {d n : ℕ} (hn : 0 < n) (hdvd : d ∣ n)
    (hs : ErdosStrausSolvable d) : ErdosStrausSolvable n := by
  obtain ⟨c, rfl⟩ := hdvd
  obtain ⟨x, y, z, hx, hy, hz, hxyz⟩ := hs
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · simp [h] at hn
    · exact h
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · simp [h] at hn
    · exact h
  refine ⟨x * c, y * c, z * c, by positivity, by positivity, by positivity, ?_⟩
  have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hc' : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  have hx' : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hy' : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hz' : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  push_cast
  have key : (1 : ℚ) / (x * c) + 1 / (y * c) + 1 / (z * c)
      = (1 / c) * ((1 : ℚ) / x + 1 / y + 1 / z) := by
    field_simp
  rw [key, hxyz]
  field_simp

/-! ### Solvable residue classes -/

/-- `4 / n` is a sum of three unit fractions whenever `n` is even. -/
