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

lemma outer_reach {i r : ℕ} (hi : i ≤ G.N) (hr : r = G.cnt x i G.N) :
    ∀ k v, v + k = G.N →
      MR G x (mkO G i r v (G.cnt x (i + 1) v)) (mkO G i r G.N (G.cnt x (i + 1) G.N)) := by
  intro k
  induction k with
  | zero =>
      intro v hv
      have : v = G.N := by omega
      subst this
      exact Relation.ReflTransGen.refl
  | succ k ih =>
      intro v hv
      have hvN : v < G.N := by omega
      have hb : G.cnt x (i + 1) v ≤ G.N := le_trans (cnt_le _ _) (by omega)
      have hstep : (machine G).edge x (mkO G i r v (G.cnt x (i + 1) v))
          (mkI G i r v (G.cnt x (i + 1) v) 0 0 false) := by
        rw [edge_iff]
        refine Or.inl ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
        · mkfin
        · mkfin
        · mkfin
      refine Relation.ReflTransGen.head hstep ?_
      have hstart : mkI G i r v (G.cnt x (i + 1) v) 0 0 false
          = mkI G i r v (G.cnt x (i + 1) v) 0 (G.cnt x i 0) (flagOf G x i 0 v) := by
        rw [cnt_zero_index, flagOf_zero]
      rw [hstart]
      exact Relation.ReflTransGen.trans (inner_reach hi hr hvN rfl G.N 0 (by omega))
        (ih (v + 1) (by omega))

/-- All the rounds of the counting algorithm. -/
