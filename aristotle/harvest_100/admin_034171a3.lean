/-
# Quadruplet 11 13 17 19
Category: Frontier — Prime Numbers
Target: Constellation.quadruplet_11_13_17_19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: the header above is written as a plain block comment `/- ... -/` rather than a
-- module docstring `/-! ... -/`, because Lean 4 requires all `import` commands to precede
-- any module docstring. The text is otherwise verbatim.

import Mathlib

namespace Constellation

/-- `(11, 13, 17, 19)` is a prime quadruplet of pattern `(0, 2, 6, 8)`:
each of `11, 13, 17, 19` is prime, and `13 = 11 + 2`, `17 = 11 + 6`, `19 = 11 + 8`.
Primality of each entry is decided by `Nat.Prime`'s decidability instance
(`Nat.decidablePrime`), invoked through `decide`. -/
theorem quadruplet_11_13_17_19 :
    Nat.Prime 11 ∧ Nat.Prime 13 ∧ Nat.Prime 17 ∧ Nat.Prime 19 ∧
      13 = 11 + 2 ∧ 17 = 11 + 6 ∧ 19 = 11 + 8 := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl, rfl⟩

end Constellation

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

