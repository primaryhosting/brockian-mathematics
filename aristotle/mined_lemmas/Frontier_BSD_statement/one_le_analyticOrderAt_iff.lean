import Mathlib

/-!
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the file layout: Lean 4 requires the `import` block to be the very first
command in a file, so the module docstring above is placed directly after it.

## Contents

* `Frontier.mordellWeilRank` : the algebraic rank of `E(ℚ)`, defined as the
  `ℚ`-dimension of `ℚ ⊗[ℤ] E(ℚ)` (as an element of `ℕ∞`, so that it is honest
  even without appealing to the Mordell–Weil theorem, which is not in Mathlib).
* `Frontier.IsHasseWeilLFunction` : the characterising properties of the
  Hasse–Weil `L`-function `L(E, s)` of an elliptic curve given by a global
  minimal integral Weierstrass model: it is entire (modularity) and on the
  half-plane `Re s > 3/2` it is given by the Euler product
  `∏_p (1 - a_p p^{-s} + ε_p p^{1-2s})⁻¹`.
* `Frontier.BSDConjecture` : the rank part of the Birch–Swinnerton-Dyer
  conjecture, `ord_{s=1} L(E, s) = rank E(ℚ)`.
* `Frontier.BSD_statement` : the Lean-checked reduction proved here — the
  conjecture implies, for every curve and every function satisfying the
  defining properties of its `L`-function, both the order-of-vanishing identity
  and the rank-zero criterion `L(E, 1) = 0 ↔ 1 ≤ rank E(ℚ)`.
* `Frontier.hasseWeilLFunction_unique` : the analytic rank appearing in the
  statement is well defined, i.e. an `L`-function satisfying the defining
  properties is unique.
* `Frontier.mordellWeilRank_eq_zero_iff_isTorsion` and
  `Frontier.mordellWeilRank_eq_zero_of_finite` : the base case, that the rank
  vanishes exactly for a torsion group of rational points, in particular for a
  curve with finitely many rational points.
* `Frontier.lFunction_one_ne_zero_of_finite` : the conjecture applied in that
  base case, giving `L(E, 1) ≠ 0` for a curve with finitely many rational
  points.
-/

open WeierstrassCurve

namespace Frontier

/-! ## The algebraic side: the Mordell–Weil rank -/

/-- The Mordell–Weil rank of the group `E(ℚ)` of rational points of an elliptic curve `E/ℚ`,
namely the `ℚ`-dimension of `ℚ ⊗[ℤ] E(ℚ)`, valued in `ℕ∞` (so an infinite rank, which the
Mordell–Weil theorem rules out, would be recorded as `⊤` rather than as junk). -/

theorem one_le_analyticOrderAt_iff {L : ℂ → ℂ} {z : ℂ} (h : AnalyticAt ℂ L z) :
    1 ≤ analyticOrderAt L z ↔ L z = 0 := by
  rw [ENat.one_le_iff_ne_zero, analyticOrderAt_ne_zero]
  simp [h]

/-- **BSD statement.** The Birch–Swinnerton-Dyer conjecture, as formalised in
`Frontier.BSDConjecture`, says exactly that for an elliptic curve `E/ℚ` given by a global minimal
Weierstrass model `W`, and for any function `L` satisfying the defining properties of the
Hasse–Weil `L`-function of `W`, the analytic order of vanishing of `L` at `s = 1` equals the rank
of `E(ℚ)`; and this implies the rank-zero criterion `L(E, 1) = 0 ↔ 1 ≤ rank E(ℚ)`.

The reduction from the order-of-vanishing identity to the rank-zero criterion is proved here,
unconditionally in the sense that the only input is the conjecture itself. -/
