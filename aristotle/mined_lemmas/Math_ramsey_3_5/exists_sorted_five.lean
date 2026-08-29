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

lemma exists_sorted_five {α : Type*} [LinearOrder α] {t : Finset α} (h : #t = 5) :
    ∃ a b c d e : α, a < b ∧ b < c ∧ c < d ∧ d < e ∧
      a ∈ t ∧ b ∈ t ∧ c ∈ t ∧ d ∈ t ∧ e ∈ t := by
  set f := t.orderIsoOfFin h
  exact ⟨f 0, f 1, f 2, f 3, f 4,
    Subtype.coe_lt_coe.2 (f.lt_iff_lt.2 (by decide)),
    Subtype.coe_lt_coe.2 (f.lt_iff_lt.2 (by decide)),
    Subtype.coe_lt_coe.2 (f.lt_iff_lt.2 (by decide)),
    Subtype.coe_lt_coe.2 (f.lt_iff_lt.2 (by decide)),
    (f 0).2, (f 1).2, (f 2).2, (f 3).2, (f 4).2⟩

