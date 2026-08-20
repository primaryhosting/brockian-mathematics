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

lemma final_reach (hnoacc : ¬ ∃ q, G.accV q ∧ G.Rch x G.N q) {r : ℕ}
    (hr : r = G.cnt x G.N G.N) :
    ∀ k u, u + k = G.N → MR G x (mkF G r u (G.cnt x G.N u)) (mkA G) := by
  intro k
  induction k with
  | zero =>
      intro u hu
      have huN : u = G.N := by omega
      subst huN
      have hb : G.cnt x u u ≤ G.N := cnt_le _ _
      refine Relation.ReflTransGen.single ?_
      rw [edge_iff]
      refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| ⟨rfl, ?_, ?_, rfl⟩
      · mkfin
      · mkfin
  | succ k ih =>
      intro u hu
      have huN : u < G.N := by omega
      have hcu : G.cnt x G.N u ≤ G.N := le_trans (cnt_le _ _) (by omega)
      by_cases hru : G.Rch x G.N u
      · have hacc : ¬ G.accV u := fun hc => hnoacc ⟨u, hc, hru⟩
        have hcs : G.cnt x G.N (u + 1) = G.cnt x G.N u + 1 := by
          rw [cnt_succ_index, if_pos hru]
        have hst0 := G.hst0
        have step1 : (machine G).edge x (mkF G r u (G.cnt x G.N u))
            (mkWF G r u (G.cnt x G.N u) G.st0 0) := by
          rw [edge_iff]
          refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, ?_, rfl, rfl, rfl, rfl, ?_, ?_⟩
          · mkfin
          · mkfin
          · mkfin
        have step2 : MR G x (mkWF G r u (G.cnt x G.N u) G.st0 0)
            (mkWF G r u (G.cnt x G.N u) u G.N) := walkF_reach r u _ G.N u le_rfl hru
        have step3 : (machine G).edge x (mkWF G r u (G.cnt x G.N u) u G.N)
            (mkF G r (u + 1) (G.cnt x G.N u + 1)) := by
          rw [edge_iff]
          refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, ?_, ?_, rfl, rfl, ?_, ?_⟩
          · mkfin
          · have h1 : ((mkWF G r u (G.cnt x G.N u) u G.N).u : ℕ) = u := by mkfin
            rw [h1]
            exact hacc
          · mkfin
          · mkfin
        refine Relation.ReflTransGen.trans (Relation.ReflTransGen.single step1)
          (Relation.ReflTransGen.trans step2 (Relation.ReflTransGen.head step3 ?_))
        rw [← hcs]
        exact ih (u + 1) (by omega)
      · have hcs : G.cnt x G.N (u + 1) = G.cnt x G.N u := by rw [cnt_succ_index, if_neg hru]
        have hstep : (machine G).edge x (mkF G r u (G.cnt x G.N u))
            (mkF G r (u + 1) (G.cnt x G.N u)) := by
          rw [edge_iff]
          refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, ?_, rfl, rfl, ?_, rfl⟩
          · mkfin
          · mkfin
        refine Relation.ReflTransGen.head hstep ?_
        rw [← hcs]
        exact ih (u + 1) (by omega)

/-- Completeness: if no accepting vertex is reachable, the counting machine accepts. -/
