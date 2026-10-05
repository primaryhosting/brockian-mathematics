import Mathlib
import RequestProject.ReingoldSlL

/-!
## Existence of universal exploration sequences

The hypothesis `CS.HasPolyUES` used in `RequestProject/ReingoldSlL.lean` asks for universal
exploration sequences of *polynomial* length; producing such short sequences is the deep part
of Reingold's theorem and is not formalised.  Here we prove, unconditionally, that universal
exploration sequences of *some* finite length always exist (`CS.exists_ues`).  This shows that
the notion is satisfiable — the only missing ingredient in `CS.HasPolyUES` is the polynomial
length bound.
-/

set_option autoImplicit false

namespace CS

namespace RotGraph

variable {n d : ℕ}

/-- The walk of length `k` only depends on the first `k` offsets. -/

lemma connMachine_invariant (G : RotGraph n d) (s t : Fin n) (k : ℕ) :
    ((connMachine n d T seq).run G ((connMachine n d T seq).init s t) k).1
        = G.walk seq (s, 0) (min k T) ∧
      ((connMachine n d T seq).run G ((connMachine n d T seq).init s t) k).2.1 = t ∧
      ((((connMachine n d T seq).run G ((connMachine n d T seq).init s t) k).2.2.1 : ℕ)
        = min k T) ∧
      (((connMachine n d T seq).run G ((connMachine n d T seq).init s t) k).2.2.2 = true
        ↔ ∃ j ≤ min k T, (G.walk seq (s, 0) j).1 = t) := by
  induction k with
  | zero =>
      refine ⟨rfl, rfl, rfl, ?_⟩
      show (decide (s = t) = true) ↔ _
      simp [RotGraph.walk]
  | succ k ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      rw [run_succ, connMachine_stepG]
      rcases Nat.lt_or_ge k T with hk | hk
      · have hm : min k T = k := min_eq_left hk.le
        have hm' : min (k+1) T = k+1 := min_eq_left hk
        rw [hm] at h1 h3 h4
        rw [hm']
        rw [if_neg (by rw [h3]; omega)]
        have hval : ((((connMachine n d T seq).run G ((connMachine n d T seq).init s t) k).2.2.1
            + 1 : Fin (T+1)) : ℕ) = k + 1 := by
          rw [Fin.val_add_one_of_lt (by rw [Fin.lt_def, h3]; simpa using hk), h3]
        refine ⟨by simp only [h1, h3]; rfl, h2, hval, ?_⟩
        simp only [Bool.or_eq_true, decide_eq_true_eq, h4, h1, h2]
        constructor
        · rintro (⟨j, hj, hjt⟩ | h)
          · exact ⟨j, by omega, hjt⟩
          · exact ⟨k+1, le_refl _, h⟩
        · rintro ⟨j, hj, hjt⟩
          rcases Nat.lt_or_ge j (k+1) with hj' | hj'
          · exact Or.inl ⟨j, by omega, hjt⟩
          · have hjk : j = k + 1 := by omega
            subst hjk
            exact Or.inr hjt
      · have hm : min k T = T := min_eq_right hk
        have hm' : min (k+1) T = T := min_eq_right (by omega)
        rw [hm] at h1 h3 h4
        rw [hm', if_pos h3]
        exact ⟨h1, h2, h3, h4⟩

