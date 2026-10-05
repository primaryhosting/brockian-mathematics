import Mathlib
/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Frontier

open SimpleGraph Finset

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) : Type := {A : Finset (Fin n) // A.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of `Fin n`, and two
distinct such subsets are adjacent when they are disjoint. -/

lemma oddWalk_adj (k : ℕ) (hk : 1 ≤ k) (j : ℕ) :
    (kneserGraph (2 * k + 1) k).Adj (oddWalk k j) (oddWalk k (j + 1)) := by
  have hstep : ((((j + 1) * k : ℕ)) : Fin (2 * k + 1))
      = (((j * k : ℕ)) : Fin (2 * k + 1)) + ((k : ℕ) : Fin (2 * k + 1)) := by
    rw [show (j + 1) * k = j * k + k by ring, Nat.cast_add]
  have hdisj : Disjoint (oddWalk k j).1 (oddWalk k (j + 1)).1 := by
    show Disjoint (cycInt k _) (cycInt k _)
    rw [hstep]
    exact cycInt_disjoint k _
  refine ⟨?_, hdisj⟩
  intro hEq
  obtain ⟨x, hx⟩ := kneser_vertex_nonempty hk (oddWalk k j)
  have hx' : x ∈ (oddWalk k (j + 1)).1 := by rw [← hEq]; exact hx
  exact (Finset.disjoint_left.mp hdisj hx) hx'

