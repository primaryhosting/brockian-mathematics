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

theorem pathGraph_four_isTree : (pathGraph 4).IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨pathGraph_connected 3, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  have h3 : (pathGraph 4).edgeFinset.card = 3 := by decide
  simp [h3]

/-- **n-Butane.** The straight-chain skeleton on four carbons has `3` C–C bonds and
`10` hydrogens: `C₄H₁₀`. -/
