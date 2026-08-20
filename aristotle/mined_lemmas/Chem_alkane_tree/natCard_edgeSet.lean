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

lemma natCard_edgeSet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Nat.card G.edgeSet = G.edgeFinset.card := by
  simp [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset]

/-- **The carbon skeleton of an acyclic alkane is a tree with `n - 1` C–C bonds.**

Let `G` be the carbon skeleton of a connected saturated hydrocarbon with `n` carbon
atoms: a simple graph on `Fin n` in which every carbon has at most four bonds (the
remaining valences being filled by hydrogen, so that the molecule has
`hydrogenCount G = ∑ v, (4 - deg v)` hydrogen atoms).

Then the molecular formula is `CₙH₂ₙ₊₂` exactly when `G` is a tree, and in that case the
number of C–C bonds is `n - 1`. -/
