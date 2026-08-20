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

lemma inv_start : Inv G x (startA G) := by
  rw [Inv_O (by rfl)]
  refine ⟨by simp [startA, mkO], ?_, by simp [startA, mkO], ?_⟩
  · have h1 : ((startA G).r : ℕ) = 1 := by
      simp [startA, mkO, fv_val (show (1 : ℕ) ≤ G.N + 1 by omega)]
    have h2 : ((startA G).i : ℕ) = 0 := by simp [startA, mkO]
    rw [h1, h2, cnt_zero_eq]
  · have h1 : ((startA G).cnt : ℕ) = 0 := by simp [startA, mkO]
    have h2 : ((startA G).v : ℕ) = 0 := by simp [startA, mkO]
    rw [h1, h2, cnt_zero_index]

/-- The invariant is preserved by every transition of the counting machine. -/
