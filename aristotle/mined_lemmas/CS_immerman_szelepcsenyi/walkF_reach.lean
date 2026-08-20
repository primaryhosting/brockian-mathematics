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

lemma walkF_reach (r u c : ℕ) :
    ∀ d w, d ≤ G.N → G.Rch x d w → MR G x (mkWF G r u c G.st0 0) (mkWF G r u c w d) := by
  intro d
  induction d with
  | zero =>
      intro w _ hw
      rw [Rch_zero] at hw
      subst hw
      exact Relation.ReflTransGen.refl
  | succ d ih =>
      intro w hd hw
      rcases hw with hw | ⟨y, hy, hedge⟩
      · refine Relation.ReflTransGen.tail (ih w (by omega) hw) ?_
        rw [edge_iff]
        refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, ?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
        · mkfin
        · mkfin
      · have hyN : y < G.N := Rch_lt hy
        have hwN : w < G.N := (G.hEd _ _ _ hedge).2
        refine Relation.ReflTransGen.tail (ih y (by omega) hy) ?_
        rw [edge_iff]
        have hwy : ((mkWF G r u c y d).w : ℕ) = y := by mkfin
        rw [hwy]
        refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, ?_, rfl, rfl, rfl, rfl, ?_, ?_⟩
        · mkfin
        · mkfin
        · have h1 : ((mkWF G r u c y d).w : ℕ) = y := by mkfin
          have h2 : ((mkWF G r u c w (d + 1)).w : ℕ) = w := by mkfin
          rw [h1, h2]
          exact hedge

/-- The final loop: enumerate all reachable vertices, check that none of them accepts, and
accept. -/
