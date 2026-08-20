import RequestProject.EulerPolyhedron

/-!
# Fullerene cages have exactly twelve pentagonal faces

A fullerene cage is a polyhedral (spherical) carbon cage in which every atom has exactly three
neighbours and every ring is a pentagon or a hexagon.  Combining Euler's formula
`V - E + F = 2` with the two incidence counts `3V = 2E` and `5p + 6h = 2E` forces the number
of pentagons to be exactly `12`, no matter how many hexagons there are.
-/

namespace Chem

open Equiv Equiv.Perm Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ### The edge involution -/

omit [Fintype α] in
/-- The edge permutation of a sphere map is an involution. -/

lemma not_sameCycle_swap_mul_of_sameCycle {π : Perm α} {x y : α} (hne : x ≠ y)
    (h : π.SameCycle x y) : ¬ (swap x y * π).SameCycle x y := by
  classical
  obtain ⟨n, hn0, -, hn⟩ := h.exists_pow_eq π
  set P : ℕ → Prop := fun m => 0 < m ∧ (π ^ m) x = y with hP
  have hex : ∃ m, P m := ⟨n, hn0, hn⟩
  set k := Nat.find hex with hk
  obtain ⟨hk0, hkx⟩ : P k := Nat.find_spec hex
  have hmin : ∀ i, 0 < i → i < k → ((π ^ i) x ≠ x ∧ (π ^ i) x ≠ y) := by
    intro i hi hik
    constructor
    · intro hcon
      have : (π ^ (k - i)) x = y := by
        have hki : k - i + i = k := by omega
        calc (π ^ (k - i)) x = (π ^ (k - i)) ((π ^ i) x) := by rw [hcon]
          _ = (π ^ (k - i + i)) x := by rw [pow_add, Perm.mul_apply]
          _ = y := by rw [hki, hkx]
      have hle : Nat.find hex ≤ k - i := Nat.find_le (⟨by omega, this⟩ : P (k - i))
      omega
    · intro hcon
      have hle : Nat.find hex ≤ i := Nat.find_le (⟨hi, hcon⟩ : P i)
      omega
  have hfix : ((swap x y * π) ^ k) x = x := by
    rw [pow_swap_mul_apply_last hk0 hmin, hkx, swap_apply_right]
  intro hcon
  obtain ⟨j, hj0, -, hj⟩ := hcon.exists_pow_eq _
  have hjk : ((swap x y * π) ^ (j % k)) x = y := by rw [pow_mod_apply hfix j, hj]
  have hlt : j % k < k := Nat.mod_lt _ hk0
  rw [pow_swap_mul_apply_eq hmin (j % k) hlt] at hjk
  rcases Nat.eq_zero_or_pos (j % k) with h0 | h0
  · rw [h0] at hjk
    simp at hjk
    exact hne hjk
  · exact (hmin (j % k) h0 hlt).2 hjk

/-- Multiplying by a transposition whose two points lie in the **same** cycle splits that
cycle: the number of orbits goes up by one. -/
