import RequestProject.Counting

/-!
# Soundness of the counting machine

We define an invariant of the states of the counting machine which is satisfied by the
initial state and preserved by every transition, and which guarantees, in the accepting
phase, that no accepting vertex is reachable.
-/

open scoped Classical

namespace CS
namespace IS

open Data

variable (G : Data) (x : List Bool)

/-- The invariant of the inner loop: the vertices counted so far form a set `S` of vertices
`< u` reachable in `i` steps, and the flag correctly records whether one of them witnesses
the reachability of `v` in `i+1` steps. -/

lemma eq_RSet_of_card {i : ℕ} {S : Finset ℕ} (hS : ∀ y ∈ S, G.Rch x i y)
    (hcard : S.card = G.cnt x i G.N) : S = RSet G x i := by
  refine Finset.eq_of_subset_of_card_le (fun y hy => (mem_RSet G x).2 (hS y hy)) ?_
  rw [card_RSet, hcard]

variable {G x}

