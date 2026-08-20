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

lemma hydrogenCount_add_twice_bonds {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 4) :
    hydrogenCount G + 2 * G.edgeFinset.card = 4 * n := by
  have hsum : (∑ v, (4 - G.degree v)) + ∑ v, G.degree v = ∑ _v : Fin n, 4 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => Nat.sub_add_cancel (hdeg v)
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges] at hsum
  simpa [hydrogenCount, mul_comm] using hsum

/-- The number of edges of a graph on `Fin n`, as a `Nat.card` of the edge set. -/
