import Mathlib
import RequestProject.KahnKalai.Iteration

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Expectation and threshold are within a log factor: a formalisation of the Park–Pham proof
of the Kahn–Kalai conjecture.
-/

open Finset

namespace Math2

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The `p`-biased measure of a family of subsets. -/

lemma sum_union_pw (a b : ℝ) (s : Finset α) (f : Finset α → ℝ) :
    ∑ W ∈ s.powerset, ∑ V ∈ s.powerset, pw a s W * pw b s V * f (W ∪ V)
      = ∑ U ∈ s.powerset, pw (1 - (1 - a) * (1 - b)) s U * f U := by
  induction s using Finset.induction_on generalizing f with
  | empty => simp [pw]
  | insert x s hx ih =>
      set c : ℝ := 1 - (1 - a) * (1 - b) with hc
      have expand : ∀ g : Finset α → Finset α → ℝ,
          ∑ W ∈ (insert x s).powerset, ∑ V ∈ (insert x s).powerset, g W V
            = ∑ W ∈ s.powerset, ((∑ V ∈ s.powerset, g W V + ∑ V ∈ s.powerset, g W (insert x V))
                + (∑ V ∈ s.powerset, g (insert x W) V
                    + ∑ V ∈ s.powerset, g (insert x W) (insert x V))) := by
        intro g
        rw [Finset.sum_powerset_insert hx]
        simp_rw [Finset.sum_powerset_insert hx]
        rw [← Finset.sum_add_distrib]
      rw [expand, Finset.sum_powerset_insert hx]
      have hsub : ∀ W ∈ s.powerset, W ⊆ s := fun W hW => Finset.mem_powerset.1 hW
      have key : ∀ W ∈ s.powerset,
          (∑ V ∈ s.powerset, pw a (insert x s) W * pw b (insert x s) V * f (W ∪ V)
            + ∑ V ∈ s.powerset, pw a (insert x s) W * pw b (insert x s) (insert x V)
                * f (W ∪ insert x V))
          + (∑ V ∈ s.powerset, pw a (insert x s) (insert x W) * pw b (insert x s) V
                * f (insert x W ∪ V)
            + ∑ V ∈ s.powerset, pw a (insert x s) (insert x W) * pw b (insert x s) (insert x V)
                * f (insert x W ∪ insert x V))
          = (1 - c) * (∑ V ∈ s.powerset, pw a s W * pw b s V * f (W ∪ V))
            + c * (∑ V ∈ s.powerset, pw a s W * pw b s V * f (insert x (W ∪ V))) := by
        intro W hW
        have hWs := hsub W hW
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
          Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun V hV => ?_)
        have hVs := hsub V hV
        rw [pw_insert_ground hx hWs, pw_insert_ground hx hVs, pw_insert_both hx hWs,
          pw_insert_both hx hVs]
        have e1 : W ∪ insert x V = insert x (W ∪ V) := by
          ext y; simp only [Finset.mem_insert, Finset.mem_union]; tauto
        have e2 : insert x W ∪ V = insert x (W ∪ V) := by
          ext y; simp only [Finset.mem_insert, Finset.mem_union]; tauto
        have e3 : insert x W ∪ insert x V = insert x (W ∪ V) := by
          ext y; simp only [Finset.mem_insert, Finset.mem_union]; tauto
        rw [e1, e2, e3, hc]
        ring
      rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ih f, ih (fun U => f (insert x U))]
      have hcs : ∀ U ∈ s.powerset, pw c (insert x s) U = pw c s U * (1 - c) :=
        fun U hU => pw_insert_ground hx (hsub U hU)
      have hcs' : ∀ U ∈ s.powerset, pw c (insert x s) (insert x U) = pw c s U * c :=
        fun U hU => pw_insert_both hx (hsub U hU)
      rw [Finset.mul_sum, Finset.mul_sum]
      refine congrArg₂ (· + ·) ?_ ?_ <;> refine Finset.sum_congr rfl (fun U hU => ?_)
      · rw [hcs U hU]; ring
      · rw [hcs' U hU]; ring

section Fintype2
variable [Fintype α]

