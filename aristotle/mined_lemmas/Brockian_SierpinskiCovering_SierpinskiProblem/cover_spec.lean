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

/-
/-!
# Sierpinski Problem
Category: Brockian Conjecture
Target: Brockian.SierpinskiCovering.SierpinskiProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
-- (The header above is wrapped in a plain block comment because Lean 4 requires
-- `import` commands to precede every other command, including module docstrings.)

import Mathlib

set_option maxHeartbeats 4000000

namespace Brockian.SierpinskiCovering

/-- `k` is a *Sierpiński number*: an odd positive integer `k` such that `k * 2 ^ n + 1`
is composite for every `n ≥ 1`. -/

lemma cover_spec : ∀ r < 36,
    1 < coverList.getD r 1 ∧ coverList.getD r 1 ≤ 73 ∧
      (78557 * 2 ^ r + 1) % coverList.getD r 1 = 0 ∧
      2 ^ 36 % coverList.getD r 1 = 1 := by
  decide

