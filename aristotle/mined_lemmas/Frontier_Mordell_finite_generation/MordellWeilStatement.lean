/-
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The doubling endomorphism `P ↦ 2 • P` of an additive commutative group. -/

def MordellWeilStatement : Prop :=
  ∀ (W : WeierstrassCurve ℚ) [W.IsElliptic], AddGroup.FG (RationalPoints W)

/-- **Mordell's theorem, as a Lean-checked reduction.**

Assume:

* (canonical/naive height machinery) every elliptic curve over `ℚ` carries a height function
  on its group of rational points satisfying the Weil height axioms `IsWeilHeight`, and
* (weak Mordell–Weil) for every elliptic curve over `ℚ` the quotient `E(ℚ) / 2 E(ℚ)` is finite.

Then the group of rational points of every elliptic curve over `ℚ` is finitely generated. -/
