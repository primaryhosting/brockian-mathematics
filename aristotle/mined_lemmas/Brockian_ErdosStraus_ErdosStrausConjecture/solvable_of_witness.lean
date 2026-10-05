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

lemma solvable_of_witness {n x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 4 * (x * y * z) = n * (y * z + x * z + x * y)) : Solvable n := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h0
    · simp at h; omega
    · exact h0
  refine ⟨x, y, z, hx, hy, hz, ?_⟩
  have hnq : (n:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hxq : (x:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hyq : (y:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hzq : (z:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  have hq : 4 * ((x:ℚ) * y * z) = n * (y * z + x * z + x * y) := by exact_mod_cast h
  field_simp
  linarith [hq]

section SmallPrimes

/-! ### Explicit solutions for the primes `p ≡ 1 [MOD 24]` below `1000` -/

