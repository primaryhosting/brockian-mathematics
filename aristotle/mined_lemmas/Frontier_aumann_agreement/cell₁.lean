/-
# Aumann Agreement
Category: Frontier Mind
Target: Frontier.aumann_agreement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Aumann Agreement
Category: Frontier Mind
Target: Frontier.aumann_agreement
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

namespace Frontier

/-- An *information partition* of a (finite) state space `Ω`: to each state `ω` it assigns the
cell `cell ω` of states that the agent cannot distinguish from `ω`.  The two axioms say that
`ω` always lies in its own cell and that the cells genuinely form a partition (two cells that
meet are equal). -/
structure InfoPartition (Ω : Type*) [DecidableEq Ω] where
  /-- The information cell of a state. -/
  cell : Ω → Finset Ω
  /-- Every state belongs to its own cell. -/
  mem_cell : ∀ ω : Ω, ω ∈ cell ω
  /-- Cells that overlap coincide, so the cells form a partition of `Ω`. -/
  cell_eq_of_mem : ∀ ω ω' : Ω, ω' ∈ cell ω → cell ω' = cell ω

/-- **Key aggregation lemma.**  Let `M` be a set of states that is a union of cells of the
information partition `cell` (i.e. `M` is closed under `cell`).  If on every cell inside `M`
the conditional weight of `E` equals `q` (written multiplicatively as
`p (E ∩ C) = q * p C`), then the same holds for `M` itself.

This is the "the posterior is a weighted average of the posteriors on the cells" step of
Aumann's argument. -/

def cell₁ : Fin 4 → Finset (Fin 4) := fun ω => if ω.val < 2 then {0, 1} else {2, 3}

/-- Agent 2's information partition of `Fin 4`: the cells are `{0,3}` and `{1,2}`. -/
