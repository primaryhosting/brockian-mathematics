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

lemma card_Aux_le (N : ℕ) : Fintype.card (Aux N) ≤ 12 * (N + 2) ^ 8 := by
  have h := Fintype.card_le_of_injective _ (Aux.enc_injective (N := N))
  refine le_trans h (le_of_eq ?_)
  simp [Fintype.card_prod, card_Phase]
  ring

/-- Turning a natural number into a counter (values are always `≤ N + 1` in practice). -/
