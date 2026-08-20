/-
# Ackermann Total
Category: Computer Science
Target: CS.ackermann_total
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not permit a module docstring `/-! ... -/` before `import`; the header is repeated
-- verbatim as a module docstring immediately after the import below.)

import Mathlib

/-!
# Ackermann Total
Category: Computer Science
Target: CS.ackermann_total
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

namespace CS

/-- The *graph* of the Ackermann recursion, described purely by its defining equations:

* `ack 0 n = n + 1`
* `ack (m+1) 0 = ack m 1`
* `ack (m+1) (n+1) = ack m (ack (m+1) n)`

`AckGraph m n v` says that the equations force the value of the Ackermann function at `(m, n)`
to be `v`.  Nothing here presupposes that such a value exists or is unique. -/
inductive AckGraph : ℕ → ℕ → ℕ → Prop
  | zero (n : ℕ) : AckGraph 0 n (n + 1)
  | succ_zero {m v : ℕ} : AckGraph m 1 v → AckGraph (m + 1) 0 v
  | succ_succ {m n v w : ℕ} : AckGraph (m + 1) n v → AckGraph m v w → AckGraph (m + 1) (n + 1) w

/-- The lexicographic order on `ℕ × ℕ`, which is the termination measure for the Ackermann
recursion, is well-founded.  (This is `IsWellFounded.wf` for the `Prod.Lex` instance in Mathlib.) -/

theorem ackGraph_iff (m n v : ℕ) : AckGraph m n v ↔ v = _root_.ack m n :=
  ⟨ackGraph_unique, fun h => h ▸ ackGraph_ack m n⟩

end CS

