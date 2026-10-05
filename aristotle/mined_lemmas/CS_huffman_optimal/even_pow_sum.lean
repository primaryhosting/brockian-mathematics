import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem even_pow_sum (n : ℕ) :
    ∀ (L : Multiset ℕ), (∀ k ∈ L, k < n) → Even ((L.map (fun k => 2 ^ (n - k))).sum) := by
  intro L
  induction L using Multiset.induction_on with
  | empty => simp
  | cons k L ih =>
      intro h
      have hk : k < n := h k (Multiset.mem_cons_self k L)
      have hL : ∀ j ∈ L, j < n := fun j hj => h j (Multiset.mem_cons_of_mem hj)
      rw [Multiset.map_cons, Multiset.sum_cons]
      refine Even.add ?_ (ih hL)
      have : n - k ≠ 0 := by omega
      exact (Nat.even_pow).2 ⟨even_two, this⟩

/-- If the length `n` is strictly larger than all other lengths, it can be decreased by one
without breaking Kraft's inequality. -/
