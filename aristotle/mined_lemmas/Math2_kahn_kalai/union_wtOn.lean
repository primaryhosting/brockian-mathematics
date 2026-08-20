/-
Minimum fragments (Park-Pham) and the key lemma: the cover built from the large
minimum fragments has small expected cost.
-/
import RequestProject.Basic

open scoped BigOperators
open Finset

namespace KahnKalai

variable {α : Type*} [DecidableEq α]

/-! ### Minimum fragments -/

/-- The candidate fragments of `S` relative to `W`: the sets `S' \ W` for edges `S'` of `H`
contained in `W ∪ S`. -/

lemma union_wtOn (a b : ℝ) (s : Finset α) : ∀ f : Finset α → ℝ,
    ∑ A ∈ s.powerset, ∑ B ∈ s.powerset, wtOn s a A * wtOn s b B * f (A ∪ B)
      = ∑ C ∈ s.powerset, wtOn s (a + b - a * b) C * f C := by
  induction s using Finset.induction_on with
  | empty => intro f; simp [wtOn]
  | insert x s hx ih =>
      intro f
      have hc : 1 - (a + b - a * b) = (1 - a) * (1 - b) := by ring
      -- abbreviation for the double sum over `s`
      set S : (Finset α → ℝ) → ℝ := fun g =>
        ∑ A ∈ s.powerset, ∑ B ∈ s.powerset, wtOn s a A * wtOn s b B * g (A ∪ B) with hS
      have hpull : ∀ (g : Finset α → ℝ) (A : Finset α),
          wtOn s a A * (∑ B ∈ s.powerset, wtOn s b B * g (A ∪ B))
            = ∑ B ∈ s.powerset, wtOn s a A * wtOn s b B * g (A ∪ B) := by
        intro g A
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun B _ => by ring)
      -- inner sums
      have hG : ∀ A : Finset α, A ⊆ s →
          (∑ B ∈ (insert x s).powerset, wtOn (insert x s) b B * f (A ∪ B))
            = (1 - b) * (∑ B ∈ s.powerset, wtOn s b B * f (A ∪ B))
              + b * (∑ B ∈ s.powerset, wtOn s b B * f (insert x (A ∪ B))) := by
        intro A _
        rw [sum_powerset_insert_wt hx b (fun B => f (A ∪ B))]
        congr 2
        refine Finset.sum_congr rfl ?_
        intro B _
        rw [Finset.union_insert]
      have hG' : ∀ A : Finset α, A ⊆ s →
          (∑ B ∈ (insert x s).powerset, wtOn (insert x s) b B * f (insert x A ∪ B))
            = (1 - b) * (∑ B ∈ s.powerset, wtOn s b B * f (insert x (A ∪ B)))
              + b * (∑ B ∈ s.powerset, wtOn s b B * f (insert x (A ∪ B))) := by
        intro A _
        rw [sum_powerset_insert_wt hx b (fun B => f (insert x A ∪ B))]
        congr 2
        · refine Finset.sum_congr rfl ?_
          intro B _
          rw [Finset.insert_union]
        · refine Finset.sum_congr rfl ?_
          intro B _
          rw [Finset.insert_union, Finset.union_insert, Finset.insert_idem]
      -- rewrite the left-hand side
      have hL : ∑ A ∈ (insert x s).powerset, ∑ B ∈ (insert x s).powerset,
            wtOn (insert x s) a A * wtOn (insert x s) b B * f (A ∪ B)
          = (1 - a) * (1 - b) * S f + (a + b - a * b) * S (fun C => f (insert x C)) := by
        have e1 : ∀ A : Finset α, (∑ B ∈ (insert x s).powerset,
              wtOn (insert x s) a A * wtOn (insert x s) b B * f (A ∪ B))
            = wtOn (insert x s) a A *
                ∑ B ∈ (insert x s).powerset, wtOn (insert x s) b B * f (A ∪ B) := by
          intro A
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun B _ => by ring)
        simp only [e1]
        rw [sum_powerset_insert_wt hx a
          (fun A => ∑ B ∈ (insert x s).powerset, wtOn (insert x s) b B * f (A ∪ B))]
        have r1 : (∑ A ∈ s.powerset, wtOn s a A *
              ∑ B ∈ (insert x s).powerset, wtOn (insert x s) b B * f (A ∪ B))
            = (1 - b) * S f + b * S (fun C => f (insert x C)) := by
          rw [hS]
          beta_reduce
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro A hA
          rw [hG A (mem_powerset.1 hA), mul_add, ← mul_assoc, ← mul_assoc]
          rw [mul_comm (wtOn s a A) (1 - b), mul_comm (wtOn s a A) b]
          rw [mul_assoc, mul_assoc, hpull f A, hpull (fun C => f (insert x C)) A]
        have r2 : (∑ A ∈ s.powerset, wtOn s a A *
              ∑ B ∈ (insert x s).powerset, wtOn (insert x s) b B * f (insert x A ∪ B))
            = S (fun C => f (insert x C)) := by
          rw [hS]
          beta_reduce
          refine Finset.sum_congr rfl ?_
          intro A hA
          rw [hG' A (mem_powerset.1 hA)]
          have : (1 - b) * (∑ B ∈ s.powerset, wtOn s b B * f (insert x (A ∪ B)))
              + b * (∑ B ∈ s.powerset, wtOn s b B * f (insert x (A ∪ B)))
              = ∑ B ∈ s.powerset, wtOn s b B * f (insert x (A ∪ B)) := by ring
          rw [this, hpull (fun C => f (insert x C)) A]
        rw [r1, r2]
        ring
      rw [hL, sum_powerset_insert_wt hx (a + b - a * b) f, hc]
      simp only [hS]
      rw [ih f, ih (fun C => f (insert x C))]

end KahnKalai

