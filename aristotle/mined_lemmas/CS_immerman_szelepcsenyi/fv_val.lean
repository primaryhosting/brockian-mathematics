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

@[simp] lemma fv_val {N k : ℕ} (h : k ≤ N + 1) : ((fv N k : Fin (N + 2)) : ℕ) = k := by
  simp [fv, Nat.min_eq_left h]

section Machine

variable (G : Data)

/-- The transition relation of the counting machine. -/
