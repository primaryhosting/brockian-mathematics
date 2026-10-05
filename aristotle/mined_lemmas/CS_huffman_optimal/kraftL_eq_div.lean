import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem kraftL_eq_div (n : ℕ) :
    ∀ (L : Multiset ℕ), (∀ k ∈ L, k ≤ n) →
      kraftL L = (((L.map (fun k => 2 ^ (n - k))).sum : ℕ) : ℝ) / 2 ^ n := by
  intro L
  induction L using Multiset.induction_on with
  | empty => simp
  | cons k L ih =>
      intro h
      have hk : k ≤ n := h k (Multiset.mem_cons_self k L)
      have hL : ∀ j ∈ L, j ≤ n := fun j hj => h j (Multiset.mem_cons_of_mem hj)
      rw [kraftL_cons, ih hL, two_zpow_neg_eq_div hk, Multiset.map_cons, Multiset.sum_cons]
      push_cast
      ring

