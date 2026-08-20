import Mathlib

/-!
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` to be the very first command of a file, so the
required header block is placed immediately after `import Mathlib`.

This file formalises the statement of the Birch--Swinnerton-Dyer conjecture

  ord_{s = 1} L(E, s) = rank E(ℚ)

for elliptic curves over `ℚ` given by a global minimal integral Weierstrass model, and proves
the rank-zero base case together with a Lean-checked reduction of the rank-zero case of the
conjecture to the equivalence `L(E, 1) ≠ 0 ↔ E(ℚ) finite`.
-/

namespace Frontier

open WeierstrassCurve

/-! ## The Mordell–Weil group and its rank -/

/-- The group `E(ℚ)` of rational points of the elliptic curve given by the integral
Weierstrass model `W` over `ℤ`. -/
abbrev RatPoints (W : WeierstrassCurve ℤ) : Type := (W.baseChange ℚ).toAffine.Point

/-- The algebraic rank of `E(ℚ)`: the rank of the Mordell–Weil group as a `ℤ`-module. -/

theorem mordellWeilRank_eq_zero_iff {W : WeierstrassCurve ℤ}
    (hfg : Module.Finite ℤ (RatPoints W)) :
    mordellWeilRank W = 0 ↔ Finite (RatPoints W) := by
  constructor
  · intro h
    have hlt : Module.rank ℤ (RatPoints W) < Cardinal.aleph0 := Module.rank_lt_aleph0 ℤ _
    have hzero : Module.rank ℤ (RatPoints W) = 0 := by
      rcases Cardinal.toNat_eq_zero.mp h with h0 | h0
      · exact h0
      · exact absurd (lt_of_le_of_lt h0 hlt) (lt_irrefl _)
    exact Module.finite_of_fg_torsion _ (rank_eq_zero_iff_isTorsion.mp hzero)
  · exact fun h => mordellWeilRank_eq_zero_of_isTorsion (isTorsion_of_finite h)

/-! ## The base case and the reduction -/

/-- **Base case of the Birch and Swinnerton-Dyer conjecture.** If the Mordell–Weil group `E(ℚ)`
is a torsion group and the `L`-function of `E` does not vanish at `s = 1`, then the BSD equality
`ord_{s = 1} L(E, s) = rank E(ℚ)` holds (both sides are `0`). -/
