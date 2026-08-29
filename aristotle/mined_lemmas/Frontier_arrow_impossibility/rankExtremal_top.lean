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
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is repeated
-- verbatim as the module docstring below.)

import Mathlib

/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

variable {A : Type*} {n : ℕ}

/-! ## Rankings and profiles -/

/-- `r` is a strict ranking (irreflexive, transitive, total) of the alternatives. -/
structure IsRanking (r : A → A → Prop) : Prop where
  asymm : ∀ x y, r x y → ¬ r y x
  trans' : ∀ x y z, r x y → r y z → r x z
  total : ∀ x y, x ≠ y → r x y ∨ r y x


lemma rankExtremal_top {b y : A} {top : Prop} (h : top) : rankExtremal b y top b = 0 := by
  classical
  simp [rankExtremal, h]

