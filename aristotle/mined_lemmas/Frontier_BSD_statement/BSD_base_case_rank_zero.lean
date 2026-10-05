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

theorem BSD_base_case_rank_zero (hBSD : BSD_statement) {W : WeierstrassCurve ℤ} {L : ℂ → ℂ}
    (hE : (W.baseChange ℚ).IsElliptic) (hmin : IsGlobalMinimalModel W) (hL : IsHasseWeilL W L)
    (htors : AddMonoid.IsTorsion (MordellWeil W)) : L 1 ≠ 0 := by
  have h := hBSD W L hE hmin hL
  rw [mwRank_eq_zero_of_isTorsion htors] at h
  simpa using ((hL.entire 1).analyticOrderAt_eq_zero).mp (by simpa using h)

/-- **Weak BSD, as a consequence of BSD.** Assuming BSD, the Mordell–Weil rank vanishes exactly
when the `L`-function does not vanish at `s = 1`. -/
