/-
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 forbids a module docstring before `import`; the required header is repeated verbatim
-- as the module docstring immediately below the import.)

import Mathlib

/-!
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

open scoped TensorProduct

/-! ## The arithmetic side: Mordell–Weil rank -/

/-- The Mordell–Weil group `E(ℚ)` of an integral Weierstrass model `W`, i.e. the group of
rational nonsingular points of the base change of `W` to `ℚ`. -/
abbrev MordellWeil (W : WeierstrassCurve ℤ) : Type := (W.baseChange ℚ).toAffine.Point

/-- The Mordell–Weil rank of `E(ℚ)`, defined as the dimension of `ℚ ⊗ℤ E(ℚ)` over `ℚ`.
For a finitely generated abelian group this is exactly the rank of its free part. -/

theorem BSD_L_ne_zero (hBSD : BSD_statement) {W : WeierstrassCurve ℤ} {L : ℂ → ℂ}
    (hE : (W.baseChange ℚ).IsElliptic) (hmin : IsGlobalMinimalModel W) (hL : IsHasseWeilL W L) :
    L ≠ 0 := by
  intro h
  refine BSD_analyticOrder_ne_top hBSD hE hmin hL ?_
  rw [analyticOrderAt_eq_top]
  filter_upwards with z
  rw [h]
  rfl

/-- **Reduction of BSD to two inequalities.** BSD holds if and only if, for every elliptic curve
over `ℚ` with global minimal model `W` and Hasse–Weil `L`-function `L`, the analytic rank is at
most the algebraic rank and the algebraic rank is at most the analytic rank. -/
