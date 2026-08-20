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

lemma mergeRel_pow (π : Perm α) (x y z : α) (i : ℕ) :
    MergeRel π x y z (((swap x y * π) ^ i) z) := by
  induction i with
  | zero => simpa using MergeRel.refl π x y z
  | succ n ih =>
      have hrw : ((swap x y * π) ^ (n + 1)) z = (swap x y * π) (((swap x y * π) ^ n) z) := by
        rw [pow_succ']; rfl
      rw [hrw]
      exact ih.trans (mergeRel_apply π x y _)

/-- Complete description of the cycles of `swap x y * π` when `x` and `y` lie in
different `π`-cycles. -/
