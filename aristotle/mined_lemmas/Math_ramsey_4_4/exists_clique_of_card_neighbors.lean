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

theorem exists_clique_of_card_neighbors {V : Type} {m p q : ℕ} (hm : RamseyProp m p (q + 1))
    (G : SimpleGraph V) (t : Finset V) (v : V) (hv : v ∈ t) (A : Finset V) (hAt : A ⊆ t)
    (hAadj : ∀ u ∈ A, G.Adj v u) (hcard : m ≤ A.card) :
    (∃ s ⊆ t, G.IsNClique (p + 1) s) ∨ (∃ s ⊆ t, Gᶜ.IsNClique (q + 1) s) := by
  rcases hm G A hcard with ⟨s, hs, hclique⟩ | ⟨s, hs, hclique⟩
  · refine Or.inl ⟨insert v s, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hv
      · exact hAt (hs hx)
    · exact hclique.insert (fun b hb => hAadj b (hs hb))
  · exact Or.inr ⟨s, fun x hx => hAt (hs hx), hclique⟩

/-- Red degree plus blue degree of a vertex inside `t` is `#t - 1`. -/
