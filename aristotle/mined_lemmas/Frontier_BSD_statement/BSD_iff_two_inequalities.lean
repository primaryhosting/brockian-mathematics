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

theorem BSD_iff_two_inequalities :
    BSD_statement ↔
      (∀ (W : WeierstrassCurve ℤ) (L : ℂ → ℂ), (W.baseChange ℚ).IsElliptic →
        IsGlobalMinimalModel W → IsHasseWeilL W L → analyticOrderAt L 1 ≤ (mwRank W : ℕ∞)) ∧
      (∀ (W : WeierstrassCurve ℤ) (L : ℂ → ℂ), (W.baseChange ℚ).IsElliptic →
        IsGlobalMinimalModel W → IsHasseWeilL W L → (mwRank W : ℕ∞) ≤ analyticOrderAt L 1) := by
  constructor
  · intro h
    exact ⟨fun W L hE hmin hL => (h W L hE hmin hL).le,
      fun W L hE hmin hL => (h W L hE hmin hL).ge⟩
  · rintro ⟨h₁, h₂⟩ W L hE hmin hL
    exact le_antisymm (h₁ W L hE hmin hL) (h₂ W L hE hmin hL)

/-- **Contrapositive form of BSD.** BSD fails exactly when some elliptic curve over `ℚ`, given by
a global minimal model with Hasse–Weil `L`-function `L`, has analytic rank different from its
Mordell–Weil rank. -/
