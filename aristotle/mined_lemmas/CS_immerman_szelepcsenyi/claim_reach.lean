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

lemma claim_reach {i r v cnt u c : ℕ} {flag : Bool} (hi : i ≤ G.N) (hu : u < G.N) (hc : c ≤ G.N)
    (hv : v < G.N) (hru : G.Rch x i u) :
    MR G x (mkI G i r v cnt u c flag)
      (mkI G i r v cnt (u + 1) (c + 1) (flag || decide (u = v ∨ G.edg x u v))) := by
  have hst0 := G.hst0
  have step1 : (machine G).edge x (mkI G i r v cnt u c flag)
      (mkW G i r v cnt u c flag G.st0 0) := by
    rw [edge_iff]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩))))
    · mkfin
    · mkfin
    · mkfin
  have step2 : MR G x (mkW G i r v cnt u c flag G.st0 0) (mkW G i r v cnt u c flag u i) :=
    walk_reach i r v cnt u c flag hi i u le_rfl hru
  refine Relation.ReflTransGen.tail (Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single step1) step2) ?_
  rw [edge_iff]
  have hwu : ((mkW G i r v cnt u c flag u i).w : ℕ) = u := by simp only [mkW, fv]; omega
  rw [hwu]
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩)))))))
  · mkfin
  · mkfin
  · mkfin
  · have h1 : ((mkW G i r v cnt u c flag u i).u : ℕ) = u := by simp only [mkW, fv]; omega
    have h2 : ((mkW G i r v cnt u c flag u i).v : ℕ) = v := by simp only [mkW, fv]; omega
    rw [h1, h2]
    simp only [mkW, mkI, Bool.or_eq_true, decide_eq_true_eq]
    exact Iff.rfl

/-- The inner loop: starting at the vertex `u` with a correct count, the machine reaches the
outer loop state for the next vertex `v+1`. -/
