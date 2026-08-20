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

theorem representable_of_dvd {d n : Nat} (hn : 0 < n) (hdvd : d ∣ n)
    (h : IsErdosStrausRepresentable d) : IsErdosStrausRepresentable n := by
  obtain ⟨k, rfl⟩ := hdvd
  obtain ⟨x, y, z, hx, hy, hz, hxyz⟩ := h
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at hn
    · exact hk
  refine ⟨k * x, k * y, k * z, ?_, ?_, ?_, ?_⟩
  · exact Nat.mul_pos hk hx
  · exact Nat.mul_pos hk hy
  · exact Nat.mul_pos hk hz
  · grind

/-- `4 / 2 = 1 / 1 + 1 / 2 + 1 / 2`. -/
