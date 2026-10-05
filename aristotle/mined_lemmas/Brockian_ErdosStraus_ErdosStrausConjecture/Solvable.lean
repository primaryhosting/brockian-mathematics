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
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ErdosStraus

/-- `Solvable n` means that `4 / n` can be written as a sum of three unit fractions
with positive (natural) denominators. -/

lemma Solvable.of_dvd {d n : ℕ} (hn : 0 < n) (hdvd : d ∣ n) (hd : Solvable d) :
    Solvable n := by
  obtain ⟨m, rfl⟩ := hdvd
  obtain ⟨x, y, z, hx, hy, hz, h⟩ := hd
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · simp [h0] at hn
    · exact h0
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · simp [h0] at hn
    · exact h0
  refine ⟨x * m, y * m, z * m, by positivity, by positivity, by positivity, ?_⟩
  have hmq : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hxq : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hyq : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hzq : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  have hdq : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
  have hsplit : (4 : ℚ) / ((d * m : ℕ) : ℚ) = ((4 : ℚ) / d) / m := by
    push_cast; field_simp
  rw [hsplit, h]
  push_cast
  field_simp

/-- Even case: `4/(2m) = 1/m + 1/m`. -/
