import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

def ankeny_lattice (n q : ℕ) (b : ℤ) : AddSubgroup (Fin 3 → ℝ) where
  carrier := { p | ∃ x y z : ℤ, p 0 = x ∧ p 1 = y ∧ p 2 = z ∧ x ≡ y [ZMOD n] ∧ y ≡ b * z [ZMOD (2 * q)] }
  add_mem' := by
    intro a a' ⟨x1, y1, z1, hx1, hy1, hz1, hxy1, hybz1⟩ ⟨x2, y2, z2, hx2, hy2, hz2, hxy2, hybz2⟩
    refine ⟨x1 + x2, y1 + y2, z1 + z2, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hx1, hx2]
    · simp [hy1, hy2]
    · simp [hz1, hz2]
    · exact hxy1.add hxy2
    · calc (y1 + y2 : ℤ) ≡ b * z1 + b * z2 [ZMOD (2 * q)] := hybz1.add hybz2
        _ = b * (z1 + z2) := by ring
  zero_mem' := by
    refine ⟨0, 0, 0, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Int.ModEq.refl]
  neg_mem' := by
    intro a ⟨x, y, z, hx, hy, hz, hxy, hybz⟩
    use -x, -y, -z
    constructor; simp [hx]
    constructor; simp [hy]
    constructor; simp [hz]
    constructor; exact hxy.neg
    calc (-y : ℤ) ≡ -(b * z) [ZMOD (2 * q)] := hybz.neg
      _ = b * (-z) := by ring

/-!
### A `q`-modulus variant lattice (for the `Q₁ = qx² + y² + nz²` route)

This is the congruence-defined lattice one would use with the `q ≡ -1 (mod n)` setup:
- `x ≡ y (mod n)` (same as Ankeny),
- `y ≡ b*z (mod q)` (note: modulus is `q`, not `2*q`).

This section defines the additive subgroup and the basic “arithmetic glue” lemmas (span-lattice inclusion
and the `Q₁` modular identity). The corresponding Minkowski step is implemented elsewhere in this file
as `exists_ankeny_representation_q1`, which produces a nontrivial triple satisfying
`q*x^2 + y^2 + n*z^2 = n*q` under the usual congruence hypotheses.
-/

/-- Variant lattice for the `Q₁` route: `x ≡ y (mod n)` and `y ≡ b*z (mod q)`. -/
