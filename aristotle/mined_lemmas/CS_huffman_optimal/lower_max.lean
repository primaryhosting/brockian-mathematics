import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem lower_max (b1 b2 : β) :
    ∀ (d y : ℕ) (N : Multiset (β × ℕ)), (∀ p ∈ N, p.2 ≤ y) →
      kraftL (klen ((b1, y + d) ::ₘ (b2, y) ::ₘ N)) ≤ 1 →
      kraftL (klen ((b1, y) ::ₘ (b2, y) ::ₘ N)) ≤ 1 := by
  intro d
  induction d with
  | zero => intro y N _ h; simpa using h
  | succ d ih =>
      intro y N hbd hK
      refine ih y N hbd ?_
      have hlt : ∀ k ∈ klen ((b2, y) ::ₘ N), k < y + (d + 1) := by
        intro k hk
        simp only [klen_cons, Multiset.mem_cons] at hk
        rcases hk with rfl | hk
        · omega
        · simp only [klen, Multiset.mem_map] at hk
          obtain ⟨p, hp, rfl⟩ := hk
          have := hbd p hp
          omega
      have := kraftL_decrement hlt (by simpa using hK)
      have hEq : y + (d + 1) - 1 = y + d := by omega
      rw [hEq] at this
      simpa using this

