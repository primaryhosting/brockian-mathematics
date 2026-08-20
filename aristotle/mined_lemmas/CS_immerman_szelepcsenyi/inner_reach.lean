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

lemma inner_reach {i r v cnt : ℕ} (hi : i ≤ G.N) (hr : r = G.cnt x i G.N) (hv : v < G.N)
    (hcnt : cnt = G.cnt x (i + 1) v) :
    ∀ k u, u + k = G.N →
      MR G x (mkI G i r v cnt u (G.cnt x i u) (flagOf G x i u v))
        (mkO G i r (v + 1) (G.cnt x (i + 1) (v + 1))) := by
  intro k
  induction k with
  | zero =>
      intro u hu
      have huN : u = G.N := by omega
      subst huN
      have hb : G.cnt x (i + 1) (v + 1) ≤ G.N := le_trans (cnt_le _ _) (by omega)
      have hb2 : G.cnt x (i + 1) v ≤ G.N := le_trans (cnt_le _ _) (by omega)
      have hb3 : G.cnt x i u ≤ G.N := cnt_le _ _
      refine Relation.ReflTransGen.single ?_
      rw [edge_iff]
      refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, ?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · mkfin
      · mkfin
      · mkfin
      · have h1 : G.cnt x (i + 1) (v + 1)
            = G.cnt x (i + 1) v + (if G.Rch x (i + 1) v then 1 else 0) := cnt_succ_index _ _
        simp only [mkI, mkO, fv, flagOf_N, decide_eq_true_eq]
        by_cases hP : G.Rch x (i + 1) v
        · rw [if_pos hP] at h1 ⊢
          omega
        · rw [if_neg hP] at h1 ⊢
          omega
  | succ k ih =>
      intro u hu
      have huN : u < G.N := by omega
      have hcu : G.cnt x i u ≤ G.N := cnt_le _ _
      by_cases hru : G.Rch x i u
      · have hcs : G.cnt x i (u + 1) = G.cnt x i u + 1 := by
          rw [cnt_succ_index, if_pos hru]
        have hfs : flagOf G x i (u + 1) v
            = (flagOf G x i u v || decide (u = v ∨ G.edg x u v)) := flagOf_succ_of hru
        refine Relation.ReflTransGen.trans (claim_reach hi huN hcu hv hru) ?_
        rw [← hcs, ← hfs]
        exact ih (u + 1) (by omega)
      · have hcs : G.cnt x i (u + 1) = G.cnt x i u := by rw [cnt_succ_index, if_neg hru]
        have hfs : flagOf G x i (u + 1) v = flagOf G x i u v := flagOf_succ_of_not hru
        have hstep : (machine G).edge x (mkI G i r v cnt u (G.cnt x i u) (flagOf G x i u v))
            (mkI G i r v cnt (u + 1) (G.cnt x i u) (flagOf G x i u v)) := by
          rw [edge_iff]
          refine Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
          · mkfin
          · mkfin
        refine Relation.ReflTransGen.head hstep ?_
        rw [← hcs, ← hfs]
        exact ih (u + 1) (by omega)

/-- The outer loop: one full round of the counting algorithm. -/
