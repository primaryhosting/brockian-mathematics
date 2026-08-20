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

def KervaireDim (n : ℕ) : Prop := ∃ j : ℕ, 2 ≤ j ∧ j ≤ 7 ∧ n = 2 ^ j - 2

/-- The admissible dimensions `2 ^ j - 2`, `2 ≤ j ≤ 7`, are exactly `2, 6, 14, 30, 62, 126`. -/
