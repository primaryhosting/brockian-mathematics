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
# Alkane Tree
Category: Chemistry
Target: Chem.alkane_tree
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Finset

/-- The number of hydrogen atoms attached to the carbon atom `v` of a carbon
skeleton `G`: carbon is tetravalent, so the valences left over after the C–C
bonds at `v` are saturated by hydrogens. -/

theorem not_isTree_of_bond_count_ne {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.edgeFinset.card ≠ n - 1) : ¬ G.IsTree := by
  intro htree
  exact h (by have := htree.card_edgeFinset; simp at this; omega)

section Butane

open SimpleGraph

instance instDecidablePathGraphAdj (n : ℕ) : DecidableRel (pathGraph n).Adj := fun u v =>
  decidable_of_iff _ (pathGraph_adj (u := u) (v := v)).symm

/-- The straight-chain skeleton on four carbons (the path graph on `Fin 4`) is a tree. -/
