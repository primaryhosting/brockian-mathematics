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
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Math2

/-! ## The singular plane curves `y ^ n = x ^ (n + 1)` and their normalization -/

/-- The plane affine curve `C_n : y ^ n = x ^ (n + 1)` over a field `k`.
For `n ≥ 2` this curve has a single singular point, at the origin
(for `n = 2` it is the classical cuspidal cubic `y ^ 2 = x ^ 3`). -/

lemma cuspJacobian_eq_zero_iff {k : Type*} [Field k] [CharZero k] {n : ℕ} (hn : 2 ≤ n)
    {p : k × k} (hp : p ∈ cuspCurve k n) :
    cuspJacobian k n p = (0, 0) ↔ p = (0, 0) := by
  constructor
  · intro hj
    simp only [cuspJacobian, Prod.mk.injEq, neg_eq_zero, mul_eq_zero] at hj
    have hnp1 : ((n : k) + 1) ≠ 0 := by
      have : ((n + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      simpa using this
    have hx : p.1 = 0 := by
      rcases hj.1 with h | h
      · exact absurd h hnp1
      · exact (pow_eq_zero_iff (by omega : n ≠ 0)).1 h
    exact cuspCurve_zero_of_fst_zero (by omega) hp hx
  · rintro rfl
    simp only [cuspJacobian, Prod.mk.injEq]
    exact ⟨by simp [zero_pow (by omega : n ≠ 0)], by simp [zero_pow (by omega : n - 1 ≠ 0)]⟩

/-- The normalization map `t ↦ (t ^ n, t ^ (n + 1))` is a resolution of singularities
of `C_n` with singular locus the origin. -/
