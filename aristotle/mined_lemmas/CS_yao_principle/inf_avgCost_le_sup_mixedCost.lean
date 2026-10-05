import Mathlib
/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace CS

variable {A X : Type*} [Fintype A] [Fintype X]

/-- Expected cost of the mixed (randomized) algorithm strategy `q` on the input `x`. -/

lemma inf_avgCost_le_sup_mixedCost [Nonempty A] [Nonempty X] (cost : A → X → ℝ)
    {p : X → ℝ} (hp : p ∈ stdSimplex ℝ X) {q : A → ℝ} (hq : q ∈ stdSimplex ℝ A) :
    (⨅ a, avgCost cost p a) ≤ ⨆ x, mixedCost cost q x := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hq0, hq1⟩ := hq
  set m := ⨅ a, avgCost cost p a with hm
  set M := ⨆ x, mixedCost cost q x with hM
  have hmle : ∀ a, m ≤ avgCost cost p a := fun a => ciInf_le (Finite.bddBelow_range _) a
  have hMle : ∀ x, mixedCost cost q x ≤ M := fun x => le_ciSup (Finite.bddAbove_range _) x
  have h1 : m = ∑ a, q a * m := by rw [← Finset.sum_mul, hq1, one_mul]
  have h2 : ∑ a, q a * m ≤ ∑ a, q a * avgCost cost p a :=
    Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hmle a) (hq0 a)
  have h3 : ∑ a, q a * avgCost cost p a = ∑ x, p x * mixedCost cost q x := by
    simp only [avgCost, mixedCost, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun a _ => by ring
  have h4 : ∑ x, p x * mixedCost cost q x ≤ ∑ x, p x * M :=
    Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hMle x) (hp0 x)
  have h5 : ∑ x, p x * M = M := by rw [← Finset.sum_mul, hp1, one_mul]
  linarith [h1, h2, h3, h4, h5]

omit [Fintype X] in
