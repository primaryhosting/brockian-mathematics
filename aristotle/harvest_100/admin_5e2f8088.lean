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
# Nat Countable
Category: Frontier — Set Theory
Target: Infinity.nat_countable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Infinity

/-- The naturals are countably infinite: `Nat` is a `Countable` type and is `Infinite`.

`Countable ℕ` follows from the injection `id : ℕ → ℕ`.  For `Infinite ℕ`, if `ℕ` were
finite it would carry a `Fintype` structure, and then `(Finset.univ.sup id) + 1` would be
a natural number bounded by `Finset.univ.sup id`, a contradiction. -/
theorem nat_countable : Countable Nat ∧ Infinite Nat := by
  refine ⟨⟨⟨id, fun _ _ h => h⟩⟩, ⟨fun h => ?_⟩⟩
  have hF : Fintype ℕ := Fintype.ofFinite ℕ
  exact absurd (Nat.lt_succ_self (hF.elems.sup id))
    (not_lt.mpr (Finset.le_sup (f := id) (hF.complete _)))

end Infinity

