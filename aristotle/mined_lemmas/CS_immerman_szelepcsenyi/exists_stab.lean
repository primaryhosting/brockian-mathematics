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

lemma exists_stab : ∃ i < G.N, ∀ v, G.Rch x (i + 1) v → G.Rch x i v := by
  classical
  by_contra hcon
  push_neg at hcon
  have key : ∀ m, m ≤ G.N → m + 1 ≤ G.cnt x m G.N := by
    intro m
    induction m with
    | zero => intro _; rw [cnt_zero_eq]
    | succ m ih =>
        intro hm
        have h1 := ih (by omega)
        have h2 : ¬ ∀ v, G.Rch x (m + 1) v → G.Rch x m v := by
          intro hstab
          obtain ⟨v, hv1, hv2⟩ := hcon m (by omega)
          exact hv2 (hstab v hv1)
        have := cnt_lt_of_not_stab (G := G) (x := x) m h2
        omega
  have h1 := key G.N le_rfl
  have h2 := cnt_le (G := G) (x := x) G.N G.N
  omega

/-- Reachability in the configuration graph is the same as reachability in at most `N` steps. -/
