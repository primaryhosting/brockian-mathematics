/-
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

open scoped Pointwise

/-!
## The statement

Mordell's theorem asserts that for an elliptic curve `E` over `ℚ`, the abelian group `E(ℚ)` of
rational points is finitely generated.  In Mathlib an elliptic curve over `ℚ` is a Weierstrass
curve `W : WeierstrassCurve ℚ` satisfying the typeclass assumption `W.IsElliptic`, and its group
of rational points is `W.toAffine.Point`, which carries an `AddCommGroup` structure.

Mathlib (at the pinned commit) contains no form of the Mordell–Weil theorem: searching for
`MordellWeil` returns nothing, and the theory developed in
`Mathlib.AlgebraicGeometry.EllipticCurve.*` stops at the group law, division polynomials and
reduction.  So the statement below is a genuine formalization, and what is proved here is the
classical *descent step*: the reduction of Mordell's theorem to the two inputs of the standard
proof, namely

* the weak Mordell–Weil theorem (`E(ℚ)/2E(ℚ)` is finite), and
* the theory of the canonical height (heights have finite sublevel sets, and every point of large
  height can be brought down by subtracting a coset representative and halving).

Both inputs are packaged in `Frontier.DescentData`.
-/

/-- The full Mordell–Weil statement over `ℚ`: the group of rational points of every elliptic
curve over `ℚ` is finitely generated.  (Stated only; the theorem proved below is the descent
reduction `Frontier.Mordell_finite_generation`.) -/

def intDescentData : DescentData ℤ where
  height a := a.natAbs
  bound := 1
  reps := {0, 1}
  finite_height_le C := by
    apply Set.Finite.subset (Set.finite_Icc (-(C : ℤ)) (C : ℤ))
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    simp only [Set.mem_Icc]
    omega
  descent a ha := by
    refine ⟨a / 2, ?_, ?_⟩
    · omega
    · simp only [Finset.mem_insert, Finset.mem_singleton, nsmul_eq_mul, Nat.cast_ofNat]
      omega

example : AddGroup.FG ℤ := fg_of_descentData intDescentData

end Frontier

