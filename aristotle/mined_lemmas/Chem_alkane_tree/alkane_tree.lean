/-
# Alkane Tree
Category: Chemistry
Target: Chem.alkane_tree
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Alkane Tree
Category: Chemistry
Target: Chem.alkane_tree
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

namespace Chem

/-- The number of hydrogen atoms attached to a carbon skeleton `G`: every carbon is
tetravalent, so a carbon `v` carries `4 - deg(v)` hydrogens. -/

theorem alkane_tree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ 4) :
    hydrogenCount G = 2 * n + 2 ↔ (G.IsTree ∧ G.edgeFinset.card = n - 1) := by
  have hcount := hydrogenCount_add_twice_bonds G hdeg
  have htree : G.IsTree ↔ G.edgeFinset.card + 1 = n := by
    rw [SimpleGraph.isTree_iff_connected_and_card, natCard_edgeSet]
    simp [hconn]
  rw [htree]
  omega

/-- Sanity check (methane, `CH₄`): the one-carbon skeleton has no C–C bonds, is a tree,
and carries `4 = 2·1 + 2` hydrogens. -/
example : hydrogenCount (⊥ : SimpleGraph (Fin 1)) = 2 * 1 + 2 := by
  decide

end Chem

