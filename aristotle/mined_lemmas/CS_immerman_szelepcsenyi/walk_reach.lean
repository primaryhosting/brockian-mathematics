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

lemma walk_reach (i r v cnt u c : ℕ) (flag : Bool) (hi : i ≤ G.N) :
    ∀ d w, d ≤ i → G.Rch x d w →
      MR G x (mkW G i r v cnt u c flag G.st0 0) (mkW G i r v cnt u c flag w d) := by
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
      · -- stay where we are
        refine Relation.ReflTransGen.tail (ih w (by omega) hw) ?_
        rw [edge_iff]
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩))))))
        · mkfin
        · mkfin
      · -- follow an edge
        have hyN : y < G.N := Rch_lt hy
        have hwN : w < G.N := (G.hEd _ _ _ hedge).2
        refine Relation.ReflTransGen.tail (ih y (by omega) hy) ?_
        rw [edge_iff]
        have hwy : ((mkW G i r v cnt u c flag y d).w : ℕ) = y := by
          simp only [mkW, fv]; omega
        rw [hwy]
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩)))))
        · mkfin
        · mkfin
        · have h1 : ((mkW G i r v cnt u c flag y d).w : ℕ) = y := by
            simp only [mkW, fv]; omega
          have h2 : ((mkW G i r v cnt u c flag w (d + 1)).w : ℕ) = w := by
            simp only [mkW, fv]; omega
          rw [h1, h2]
          exact hedge

/-- One iteration of the inner loop, when the vertex `u` is claimed (and is) reachable. -/
