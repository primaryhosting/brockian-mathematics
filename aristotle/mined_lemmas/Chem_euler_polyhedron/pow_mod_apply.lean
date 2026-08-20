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

lemma pow_mod_apply {π : Perm α} {x : α} {m : ℕ} (hm : (π ^ m) x = x) (i : ℕ) :
    (π ^ (i % m)) x = (π ^ i) x := by
  have key : ∀ k : ℕ, (π ^ (m * k)) x = x := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
        have : m * (n + 1) = m * n + m := by ring
        rw [this, pow_add, Perm.mul_apply, hm, ih]
  conv_rhs => rw [show i = i % m + m * (i / m) from (Nat.mod_add_div i m).symm]
  rw [pow_add, Perm.mul_apply, key]

omit [DecidableEq α] [Fintype α] in
