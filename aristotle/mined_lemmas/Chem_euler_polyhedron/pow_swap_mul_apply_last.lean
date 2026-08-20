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

lemma pow_swap_mul_apply_last {π : Perm α} {x y : α} {N : ℕ} (hN : 0 < N)
    (h : ∀ i, 0 < i → i < N → ((π ^ i) x ≠ x ∧ (π ^ i) x ≠ y)) :
    ((swap x y * π) ^ N) x = (swap x y) ((π ^ N) x) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : n < n + 1 := Nat.lt_succ_self n
  have := pow_swap_mul_apply_eq h n hn
  rw [pow_succ', pow_succ']
  simp [this]

omit [DecidableEq α] in
