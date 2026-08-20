/-
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
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

/-- The counting function of a set of naturals: the number of elements of `A` below `n`. -/

theorem szemeredi_of_finitary (h : FinitarySzemeredi) : SzemerediStatement := by
  intro A hA k
  obtain ⟨ε, hε, hcount⟩ := exists_pos_frequently_count hA
  obtain ⟨N, hN⟩ := h k ε hε
  obtain ⟨n, hn, -, hcard⟩ := hcount N
  obtain ⟨a, d, hd, hmem⟩ := hN n hn ((Finset.range n).filter (· ∈ A))
    (Finset.filter_subset _ _) hcard
  exact ⟨a, d, hd, fun i hi => (Finset.mem_filter.mp (hmem i hi)).2⟩

/-- Sanity check (non-vacuity): the whole of `ℕ` has upper density `1`, so the hypothesis of
positive upper density is satisfiable. -/
