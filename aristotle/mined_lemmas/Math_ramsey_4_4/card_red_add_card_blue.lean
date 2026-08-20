/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Math

open Finset

/-- `RamseyProp N p q` says: for every red/blue colouring of the edges of a complete graph
(the red edges being the edges of a simple graph `G`), every set `t` of at least `N` vertices
contains a red clique of size `p` or a blue clique of size `q`.
Here "blue" means an edge of the complement `Gᶜ`. -/

theorem card_red_add_card_blue {V : Type} (G : SimpleGraph V) (t : Finset V) (v : V) (hv : v ∈ t) :
    {u ∈ t.erase v | G.Adj v u}.card + {u ∈ t.erase v | Gᶜ.Adj v u}.card = t.card - 1 := by
  have h : {u ∈ t.erase v | Gᶜ.Adj v u} = {u ∈ t.erase v | ¬ G.Adj v u} := by
    refine Finset.filter_congr ?_
    intro u hu
    have hne : v ≠ u := ((Finset.mem_erase.mp hu).1).symm
    simp [SimpleGraph.compl_adj, hne]
  rw [h, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv]

/-- Both the red degree and the blue degree of any vertex are bounded, if there is no red
`(p+1)`-clique and no blue `(q+1)`-clique. -/
