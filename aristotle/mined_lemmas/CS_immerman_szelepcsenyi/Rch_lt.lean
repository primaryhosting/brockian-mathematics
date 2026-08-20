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

lemma Rch_lt : ∀ {i v : ℕ}, G.Rch x i v → v < G.N := by
  intro i
  induction i with
  | zero => intro v hv; rw [Rch_zero] at hv; have := G.hst0; omega
  | succ i ih =>
      intro v hv
      rcases hv with hv | ⟨u, _, he⟩
      · exact ih hv
      · exact (G.hEd _ _ _ he).2

variable (G x)

/-- The number of vertices `< k` reachable in at most `i` steps. -/
