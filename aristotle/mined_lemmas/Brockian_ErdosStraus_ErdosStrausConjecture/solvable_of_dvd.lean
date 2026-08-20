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

/-!
`ErdosStrausConjecture` is a well-known open problem, so this file does not prove it
outright.  What is proved here, unconditionally and axiom-cleanly, is:

* `solvable_of_dvd`: solvability passes from a divisor to any positive multiple;
* explicit parametric solutions for `n` even, `3 ∣ n`, `n ≡ 3 (mod 4)`, `n ≡ 2 (mod 3)`
  and `n ≡ 5 (mod 8)`;
* `solvable_of_mod_24_ne_one`: the conjecture holds for every `n ≥ 2` with `n % 24 ≠ 1`;
* `erdosStrausConjecture_iff_primes`: the conjecture is *equivalent* to its special case
  for primes `p ≡ 1 (mod 24)`.
-/

namespace Brockian.ErdosStraus

/-- `Solvable n` says that `4 / n` can be written as a sum of three (not necessarily
distinct) positive unit fractions. -/

theorem solvable_of_dvd {d n : ℕ} (hd : d ∣ n) (hn : 0 < n) (h : Solvable d) : Solvable n := by
  obtain ⟨m, rfl⟩ := hd
  obtain ⟨x, y, z, hx, hy, hz, hxyz⟩ := h
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp at hn
    · exact hm
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · simp at hn
    · exact hd0
  refine ⟨x * m, y * m, z * m, by positivity, by positivity, by positivity, ?_⟩
  have hxQ : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hyQ : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hzQ : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have key : (1 : ℚ) / (x * m) + 1 / (y * m) + 1 / (z * m)
      = ((1 : ℚ) / x + 1 / y + 1 / z) / m := by
    field_simp
  push_cast
  rw [key, ← hxyz, div_div]

/-- `4 / 2 = 1/1 + 1/2 + 1/2`. -/
