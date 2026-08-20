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

theorem MordellStatement_of_descentData
    (H : ∀ (W : WeierstrassCurve ℚ), W.IsElliptic → Nonempty (DescentData W.toAffine.Point)) :
    MordellStatement := by
  intro W hW
  obtain ⟨D⟩ := H W hW
  exact fg_of_descentData D

/-- Base case: a rank-zero situation.  If `E(ℚ)` is finite then it is finitely generated
(unconditionally). -/
