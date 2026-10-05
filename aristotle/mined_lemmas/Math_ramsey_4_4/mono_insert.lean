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

We show that the two-colour Ramsey number `R(4,4)` equals `18`:

* every symmetric two-colouring of the edges of the complete graph on `18` vertices
  contains a monochromatic set of `4` vertices;
* there is a symmetric two-colouring of the edges of the complete graph on `17` vertices
  (the Paley graph of order `17`) with no monochromatic set of `4` vertices.
-/

namespace Math

open Finset

/-- `MonoSet f b S` says that every pair of distinct vertices of `S` receives colour `b`. -/

lemma mono_insert (hsym : ∀ x y, f x y = f y x) {b : Bool} {W S : Finset V} {v : V}
    (hv : v ∈ W) (hS : S ⊆ nbr f b W v) (hm : MonoSet f b S) :
    insert v S ⊆ W ∧ (insert v S).card = S.card + 1 ∧ MonoSet f b (insert v S) := by
  have hvS : v ∉ S := fun h => (mem_nbr.mp (hS h)).2.1 rfl
  refine ⟨?_, Finset.card_insert_of_notMem hvS, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hv
    · exact nbr_subset (hS hx)
  · intro i hi j hj hij
    rcases Finset.mem_insert.mp hi with hi | hi <;> rcases Finset.mem_insert.mp hj with hj | hj
    · exact absurd (hi.trans hj.symm) hij
    · rw [hi]; exact (mem_nbr.mp (hS hj)).2.2
    · rw [hj, hsym]; exact (mem_nbr.mp (hS hi)).2.2
    · exact hm i hi j hj hij

/-- Either `A` contains an edge of colour `b`, or any `n` of its vertices form a
`!b`-monochromatic set. -/
