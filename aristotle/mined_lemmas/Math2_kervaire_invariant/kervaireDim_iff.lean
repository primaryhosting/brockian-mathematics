/-
/-!
# Kervaire Invariant
Category: Frontier Math
Target: Math2.kervaire_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the required header
-- appears verbatim above inside a block comment, and again as the module docstring below.)

import Mathlib

/-!
# Kervaire Invariant
Category: Frontier Math
Target: Math2.kervaire_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math2

/-- The set of dimensions allowed by the Hill–Hopkins–Ravenel theorem together with Browder's
theorem: `n = 2 ^ j - 2` with `2 ≤ j ≤ 7`. -/

theorem kervaireDim_iff (n : ℕ) :
    KervaireDim n ↔ n = 2 ∨ n = 6 ∨ n = 14 ∨ n = 30 ∨ n = 62 ∨ n = 126 := by
  constructor
  · rintro ⟨j, hj2, hj7, rfl⟩
    interval_cases j <;> norm_num
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨2, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨4, by norm_num⟩
    · exact ⟨5, by norm_num⟩
    · exact ⟨6, by norm_num⟩
    · exact ⟨7, by norm_num⟩

/-- If `2 ^ j - 2 ≤ 126`, then `j ≤ 7`. -/
