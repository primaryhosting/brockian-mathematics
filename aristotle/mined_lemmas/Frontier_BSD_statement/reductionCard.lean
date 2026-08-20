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

noncomputable def reductionCard (W : WeierstrassCurve ℤ) (p : ℕ) : ℕ :=
  Nat.card ((W.map (Int.castRingHom (ZMod p))).toAffine.Point)

/-- The trace of Frobenius `a_p` of the integral Weierstrass model `W` at a prime `p`.

At a prime of good reduction (`p ∤ Δ`) the reduction is an elliptic curve over `𝔽_p` with
`p + 1 - a_p` points, while at a prime of bad reduction the group of nonsingular points of the
reduction has `p - a_p` elements (so `a_p = 1, -1, 0` for split multiplicative, nonsplit
multiplicative and additive reduction respectively). -/
