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

namespace Math2

variable (k : Type*) [Field k]

/-- The affine plane curve `C_{a,b} : y^a = x^b` over a field `k`.
For `a, b ≥ 2` coprime this is the standard quasi-homogeneous plane curve singularity
(for `(a,b) = (2,3)` it is the cuspidal cubic `y² = x³`). -/

lemma cuspParam_range {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    Set.range (cuspParam k a b) = cuspCurve k a b := by
  obtain ⟨u, v, hinv⟩ := cuspParam_inverse (k := k) ha hb hab
  apply Set.Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    exact cuspParam_mem a b t
  · intro p hp
    by_cases h0 : p = 0
    · exact ⟨0, by simp [cuspParam, zero_pow ha.ne', zero_pow hb.ne', h0]⟩
    · exact ⟨p.1 ^ u * p.2 ^ v, hinv p hp h0⟩

/-- The curve is exactly the zero set of `cuspPoly`. -/
