/-
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Classical

namespace Frontier

/-! ## The multiplication-by-`m` subgroup and its quotient -/

/-- Multiplication by `m` as an endomorphism of an additive commutative group. -/

def MordellWeilStatement : Prop :=
  ∀ (E : WeierstrassCurve ℚ), E.IsElliptic → AddGroup.FG E.toAffine.Point

/-- **Mordell's theorem, reduced to weak Mordell–Weil plus the theory of heights.**

Let `E` be an elliptic curve over `ℚ` and let `h` be a height function on the group `E(ℚ)`
of rational points satisfying the three standard properties of the (logarithmic) canonical
height:

* for each fixed `Q ∈ E(ℚ)` there is a constant `C` with `h (P + Q) ≤ 2 * h P + C`;
* there is a constant `C` with `4 * h P ≤ h (2 • P) + C`;
* for each `C`, only finitely many points have height at most `C` (Northcott property).

If moreover the weak Mordell–Weil group `E(ℚ)/2E(ℚ)` is finite, then `E(ℚ)` is a
finitely generated abelian group.

(The hypothesis that `E` is elliptic is kept for faithfulness to the statement; the argument
itself only uses the group structure on the set of nonsingular rational points.) -/
