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

lemma round_reach : ∀ m i, i + m = G.N →
    MR G x (mkO G i (G.cnt x i G.N) 0 0) (mkO G G.N (G.cnt x G.N G.N) 0 0) := by
  intro m
  induction m with
  | zero =>
      intro i hi
      have : i = G.N := by omega
      subst this
      exact Relation.ReflTransGen.refl
  | succ m ih =>
      intro i hi
      have hiN : i < G.N := by omega
      have hb : G.cnt x (i + 1) G.N ≤ G.N := cnt_le _ _
      have hb2 : G.cnt x i G.N ≤ G.N := cnt_le _ _
      have h1 : MR G x (mkO G i (G.cnt x i G.N) 0 0)
          (mkO G i (G.cnt x i G.N) G.N (G.cnt x (i + 1) G.N)) := by
        have h := outer_reach (G := G) (x := x) (i := i) (r := G.cnt x i G.N) (by omega) rfl
          G.N 0 (by omega)
        rwa [cnt_zero_index] at h
      have hstep : (machine G).edge x (mkO G i (G.cnt x i G.N) G.N (G.cnt x (i + 1) G.N))
          (mkO G (i + 1) (G.cnt x (i + 1) G.N) 0 0) := by
        rw [edge_iff]
        refine Or.inr <| Or.inl ⟨rfl, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
        · mkfin
        · mkfin
        · mkfin
        · mkfin
        · mkfin
        · mkfin
      exact Relation.ReflTransGen.trans h1
        (Relation.ReflTransGen.head hstep (ih (i + 1) (by omega)))

/-- A guessed path can be followed by the machine inside the final loop. -/
