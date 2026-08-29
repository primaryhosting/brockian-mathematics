import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem kraftL_decrement {n : ℕ} {L : Multiset ℕ} (h : ∀ k ∈ L, k < n)
    (hK : kraftL (n ::ₘ L) ≤ 1) : kraftL ((n - 1) ::ₘ L) ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hK
  set S : ℕ := (L.map (fun k => 2 ^ (n - k))).sum with hS
  have hLn : ∀ k ∈ L, k ≤ n := fun k hk => le_of_lt (h k hk)
  have h1 : kraftL (n ::ₘ L) = ((1 + S : ℕ) : ℝ) / 2 ^ n := by
    rw [kraftL_eq_div n _ (by
      intro k hk
      rcases Multiset.mem_cons.1 hk with rfl | hk
      · exact le_refl _
      · exact hLn k hk)]
    simp [hS]
  have h2 : kraftL ((n - 1) ::ₘ L) = ((2 + S : ℕ) : ℝ) / 2 ^ n := by
    rw [kraftL_eq_div n _ (by
      intro k hk
      rcases Multiset.mem_cons.1 hk with rfl | hk
      · omega
      · exact hLn k hk)]
    congr 1
    simp only [Multiset.map_cons, Multiset.sum_cons, ← hS]
    have : n - (n - 1) = 1 := by omega
    rw [this]
    push_cast
    ring
  rw [h1, div_le_one (by positivity)] at hK
  have hnat : 1 + S ≤ 2 ^ n := by
    have : ((1 + S : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by push_cast; exact_mod_cast hK
    exact_mod_cast this
  have hev : Even S := even_pow_sum n L h
  have hev2 : Even (2 ^ n) := (Nat.even_pow).2 ⟨even_two, by omega⟩
  have hne : 1 + S ≠ 2 ^ n := by
    intro hcon
    obtain ⟨m, hm⟩ := hev
    obtain ⟨j, hj⟩ := hev2
    omega
  have hnat2 : 2 + S ≤ 2 ^ n := by omega
  rw [h2, div_le_one (by positivity)]
  calc ((2 + S : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast hnat2
    _ = 2 ^ n := by push_cast; ring

/-! ### Cost of a weighted length assignment -/

variable {β : Type*}

/-- The multiset of lengths occurring in a length assignment. -/
