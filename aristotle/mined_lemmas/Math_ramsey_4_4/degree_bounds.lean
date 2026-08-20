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

theorem degree_bounds {V : Type} {m n p q : ℕ} (hm : RamseyProp m p (q + 1))
    (hn : RamseyProp n (p + 1) q) (G : SimpleGraph V) (t : Finset V)
    (h1 : ¬ ∃ s ⊆ t, G.IsNClique (p + 1) s) (h2 : ¬ ∃ s ⊆ t, Gᶜ.IsNClique (q + 1) s)
    (v : V) (hv : v ∈ t) :
    {u ∈ t.erase v | G.Adj v u}.card < m ∧ {u ∈ t.erase v | Gᶜ.Adj v u}.card < n := by
  constructor
  · by_contra hA
    push_neg at hA
    rcases exists_clique_of_card_neighbors hm G t v hv _
      (fun x hx => Finset.mem_of_mem_erase (Finset.mem_filter.mp hx).1)
      (fun u hu => (Finset.mem_filter.mp hu).2) hA with h | h
    · exact h1 h
    · exact h2 h
  · by_contra hB
    push_neg at hB
    rcases exists_clique_of_card_neighbors (RamseyProp.symm hn) Gᶜ t v hv _
      (fun x hx => Finset.mem_of_mem_erase (Finset.mem_filter.mp hx).1)
      (fun u hu => (Finset.mem_filter.mp hu).2) hB with h | h
    · exact h2 h
    · rw [compl_compl] at h
      exact h1 h

/-- `R(p+1, q+1) ≤ R(p, q+1) + R(p+1, q)`. -/
