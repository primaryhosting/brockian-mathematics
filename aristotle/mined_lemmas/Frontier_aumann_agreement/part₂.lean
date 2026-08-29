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

def part₂ : InfoPartition (Fin 4) where
  cell := cell₂
  mem_cell := by decide
  cell_eq_of_mem := by decide

/-- All hypotheses of `Frontier.aumann_agreement` are satisfiable with distinct partitions
and a non-trivial common posterior value `1/2`. -/
example :
    (1 : ℝ) / 2 = 1 / 2 := by
  refine aumann_agreement (p := fun _ => (1 / 4 : ℝ)) part₁ part₂ {0, 2} Finset.univ
    (fun _ _ => Finset.subset_univ _) (fun _ _ => Finset.subset_univ _) ?_ ?_ ?_ (1 / 2) (1 / 2)
    ?_ ?_
  · intro ω _
    have h : (part₁.cell ω).card = 2 := by revert ω; decide
    rw [Finset.sum_const, h]; norm_num
  · intro ω _
    have h : (part₂.cell ω).card = 2 := by revert ω; decide
    rw [Finset.sum_const, h]; norm_num
  · rw [Finset.sum_const, Finset.card_univ]; norm_num
  · intro ω _
    have h : (part₁.cell ω ∩ ({0, 2} : Finset (Fin 4))).card = 1 ∧ (part₁.cell ω).card = 2 := by
      revert ω; decide
    rw [Finset.sum_const, Finset.sum_const, h.1, h.2]; norm_num
  · intro ω _
    have h : (part₂.cell ω ∩ ({0, 2} : Finset (Fin 4))).card = 1 ∧ (part₂.cell ω).card = 2 := by
      revert ω; decide
    rw [Finset.sum_const, Finset.sum_const, h.1, h.2]; norm_num

end Example

end Frontier

