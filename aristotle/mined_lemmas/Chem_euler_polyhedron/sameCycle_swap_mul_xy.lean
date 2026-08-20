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

lemma sameCycle_swap_mul_xy {π : Perm α} {x y : α} (hxy : ¬ π.SameCycle x y) :
    (swap x y * π).SameCycle x y := by
  classical
  obtain ⟨m, hm0, hm⟩ := exists_pos_pow_apply_eq_self π x
  set P : ℕ → Prop := fun n => 0 < n ∧ (π ^ n) x = x with hP
  have hex : ∃ n, P n := ⟨m, hm0, hm⟩
  set k := Nat.find hex with hk
  obtain ⟨hk0, hkx⟩ : P k := Nat.find_spec hex
  have hmin : ∀ i, 0 < i → i < k → ((π ^ i) x ≠ x ∧ (π ^ i) x ≠ y) := by
    intro i hi hik
    constructor
    · intro hcon
      have hle : Nat.find hex ≤ i := Nat.find_le (⟨hi, hcon⟩ : P i)
      omega
    · intro hcon
      exact hxy (hcon ▸ sameCycle_of_pow i)
  have : ((swap x y * π) ^ k) x = y := by
    rw [pow_swap_mul_apply_last hk0 hmin, hkx, swap_apply_left]
  exact ⟨(k : ℤ), by simpa using this⟩

omit [Fintype α] in
/-- Elements outside the cycles of `x` and `y` are unaffected. -/
