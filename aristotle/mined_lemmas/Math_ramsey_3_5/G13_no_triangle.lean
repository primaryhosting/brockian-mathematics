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
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset SimpleGraph

namespace Ramsey35

variable {V : Type*} [DecidableEq V]

/-! ### Basic clique helpers -/

omit [DecidableEq V] in
/-- A finset all of whose distinct pairs are non-adjacent is a clique in the complement. -/

lemma G13_no_triangle : ∀ a b c : Fin 13, ¬ (adjB a b ∧ adjB b c ∧ adjB a c) := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
