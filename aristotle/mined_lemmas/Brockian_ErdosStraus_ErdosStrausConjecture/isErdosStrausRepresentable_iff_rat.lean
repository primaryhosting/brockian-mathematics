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

/-!
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ErdosStraus

/-- `IsErdosStrausRepresentable n` says that `4 / n` is a sum of three positive unit fractions,
`4 / n = 1 / x + 1 / y + 1 / z`, written here in the equivalent denominator-cleared form
`4 * (x * y * z) = n * (y * z + x * z + x * y)` with `x, y, z > 0`.
(The three denominators are not required to be distinct.) -/

theorem isErdosStrausRepresentable_iff_rat {n : ℕ} (hn : 0 < n) :
    IsErdosStrausRepresentable n ↔ IsErdosStrausRepresentableRat n := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  constructor
  · rintro ⟨x, y, z, hx, hy, hz, h⟩
    refine ⟨x, y, z, hx, hy, hz, ?_⟩
    have hx' : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
    have hy' : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
    have hz' : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
    have h' : (4 : ℚ) * (x * y * z) = n * (y * z + x * z + x * y) := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) h
    field_simp
    linarith [h']
  · rintro ⟨x, y, z, hx, hy, hz, h⟩
    refine ⟨x, y, z, hx, hy, hz, ?_⟩
    have hx' : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
    have hy' : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
    have hz' : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
    have h' : (4 : ℚ) * (x * y * z) = n * (y * z + x * z + x * y) := by
      field_simp at h
      linarith [h]
    exact_mod_cast h'

/-- `IsPrimeNat` agrees with Mathlib's `Nat.Prime`. -/
