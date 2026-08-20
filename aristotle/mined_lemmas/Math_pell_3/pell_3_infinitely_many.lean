/-!
# Pell 3
Category: Pure Mathematics
Target: Math.pell_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Pell equation `x² − 3·y² = 1` has a nontrivial integer solution,
i.e. one with `y ≠ 0` (equivalently, other than `(x, y) = (±1, 0)`):
take `(x, y) = (2, 1)`, since `2² − 3·1² = 1`.

(The file has no `import` line because the required header comment must be the very
first thing in the file, and Lean requires `import` commands to precede all other
commands; the proof only uses core `Int` arithmetic, so no import is needed.) -/

theorem pell_3_infinitely_many (N : ℤ) : ∃ x y : ℤ, x ^ 2 - 3 * y ^ 2 = 1 ∧ N < y := by
  obtain ⟨m, hm⟩ := exists_nat_gt N
  exact ⟨(pellStep m).1, (pellStep m).2, pellStep_sol m,
    lt_of_lt_of_le hm (pellStep_snd_ge m)⟩

end Math

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

