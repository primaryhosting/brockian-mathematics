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

lemma pow_swap_mul_apply_of_not_mem {π : Perm α} {x y z : α} (hzx : ¬ π.SameCycle z x)
    (hzy : ¬ π.SameCycle z y) : ∀ i : ℕ, ((swap x y * π) ^ i) z = (π ^ i) z := by
  intro i
  induction i with
  | zero => simp
  | succ n ih =>
      have hne : (π ^ (n + 1)) z ≠ x ∧ (π ^ (n + 1)) z ≠ y := by
        constructor
        · intro hcon
          exact hzx (hcon ▸ sameCycle_of_pow (n + 1))
        · intro hcon
          exact hzy (hcon ▸ sameCycle_of_pow (n + 1))
      have h1 : ((swap x y * π) ^ (n + 1)) z = (swap x y) (π ((π ^ n) z)) := by
        rw [pow_succ']
        simp [ih]
      have h2 : (π ^ (n + 1)) z = π ((π ^ n) z) := by rw [pow_succ']; rfl
      rw [h1, ← h2, swap_apply_of_ne_of_ne hne.1 hne.2]

