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

lemma pow_swap_mul_apply_eq {π : Perm α} {x y : α} {N : ℕ}
    (h : ∀ i, 0 < i → i < N → ((π ^ i) x ≠ x ∧ (π ^ i) x ≠ y)) :
    ∀ i, i < N → ((swap x y * π) ^ i) x = (π ^ i) x := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ n ih =>
      intro hn
      have hn' : n < N := Nat.lt_of_succ_lt hn
      have hstep : ((swap x y * π) ^ (n + 1)) x = (swap x y) (π ((π ^ n) x)) := by
        rw [pow_succ']
        simp [ih hn']
      rw [hstep]
      have hx : (π ^ (n + 1)) x = π ((π ^ n) x) := by
        rw [pow_succ']; rfl
      rw [← hx]
      have := h (n + 1) (Nat.succ_pos n) hn
      rw [swap_apply_of_ne_of_ne this.1 this.2]

omit [Fintype α] in
