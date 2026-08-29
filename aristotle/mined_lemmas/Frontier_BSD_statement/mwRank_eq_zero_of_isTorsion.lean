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

theorem mwRank_eq_zero_of_isTorsion {W : WeierstrassCurve ℤ}
    (h : AddMonoid.IsTorsion (MordellWeil W)) : mwRank W = 0 := by
  have : Subsingleton (ℚ ⊗[ℤ] MordellWeil W) := subsingleton_rat_tensor_of_isTorsion _ h
  simp [mwRank, Module.finrank_zero_of_subsingleton]

/-! ## Lean-checked reductions of BSD -/

/-- **Reduction of BSD to a nonvanishing statement in rank 0.** Assuming BSD, an elliptic curve
whose rational points are all torsion has nonvanishing `L`-value at `s = 1`. This is the base case
`rank = 0 ⟹ L(E, 1) ≠ 0` of the conjecture. -/
