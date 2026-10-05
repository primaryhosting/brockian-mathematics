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

lemma cuspParam_eq_zero_iff {k : Type*} [Field k] {n : ℕ} (hn : 1 ≤ n) (t : k) :
    cuspParam k n t = (0, 0) ↔ t = 0 := by
  constructor
  · intro h
    simp only [cuspParam, Prod.mk.injEq] at h
    exact (pow_eq_zero_iff (by omega : n ≠ 0)).1 h.1
  · rintro rfl
    simp [cuspParam, zero_pow (by omega : n ≠ 0), zero_pow (by omega : n + 1 ≠ 0)]

