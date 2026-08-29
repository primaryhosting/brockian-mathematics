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
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Header kept verbatim, except that it is a plain block comment `/- -/` rather than a
-- module docstring `/-! -/`: Lean 4 does not allow any command, including a module
-- docstring, to precede the `import` section of a file.)

import Mathlib

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; for `n ≥ 1`
this agrees with the usual integer definition). -/

lemma lt_of_woodall_lt {m n : ℕ} (hn : 1 ≤ n) (h : woodall m < woodall n) : m < n := by
  by_contra hcon
  exact absurd (woodall_le_woodall hn (Nat.le_of_not_lt hcon)) (not_le.mpr h)

end Basic

section Examples

