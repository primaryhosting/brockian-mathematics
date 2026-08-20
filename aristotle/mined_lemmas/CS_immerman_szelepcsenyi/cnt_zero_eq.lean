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

lemma cnt_zero_eq : G.cnt x 0 G.N = 1 := by
  classical
  unfold cnt
  have : (Finset.range G.N).filter (fun v => G.Rch x 0 v) = {G.st0} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hv⟩; exact hv
    · rintro rfl; exact ⟨G.hst0, rfl⟩
  rw [this]; simp

