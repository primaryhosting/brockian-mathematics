import Mathlib

/-!
# A model of relativized (oracle) polynomial-time computation

We fix a small imperative programming language over string-valued registers,
with an oracle-query primitive and a nondeterministic guess primitive, and an
explicit step-cost semantics.  This is the machine model used to define the
relativized classes `P^O` and `NP^O`.
-/

namespace BGS

/-- Binary strings. -/
abbrev Str := List Bool

/-- An oracle is a set of strings (given as a predicate). -/
abbrev Oracle := Str → Prop

/-- A register file: countably many string-valued registers. -/
abbrev Regs := ℕ → Str

/-- Update a register. -/

theorem inP_imp_inNP {O : Oracle} {L : Str → Prop} (h : inP O L) : inNP O L := by
  obtain ⟨s, k, hng, hs⟩ := h
  refine ⟨s, k, fun x => ?_⟩
  obtain ⟨σ', c, tr, hrun, hc, hacc⟩ := hs x
  constructor
  · intro hL
    exact ⟨σ', c, tr, hrun, hc, hacc.2 hL⟩
  · rintro ⟨σ'', c', tr', hrun', hc', hacc'⟩
    obtain ⟨e1, e2, e3⟩ := Exec.det hng hrun' hrun
    exact hacc.1 (e1 ▸ hacc')

end BGS

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

