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

noncomputable def pointCountModP (W : WeierstrassCurve ℤ) (p : ℕ) : ℕ :=
  Nat.card (W.baseChange (ZMod p)).toAffine.Point

/-- `W` has good reduction at `p` when `p` does not divide the discriminant of `W`.
(For a global minimal model this is the usual notion of good reduction.) -/
abbrev HasGoodReductionAt (W : WeierstrassCurve ℤ) (p : ℕ) : Prop := ¬ p ∣ W.Δ.natAbs

/-- The `p`-th coefficient of the Hasse–Weil `L`-function. At a prime of good reduction this is
the trace of Frobenius `a_p = p + 1 - #E(𝔽_p)`. At a prime of bad reduction it is
`a_p = p - #E_ns(𝔽_p)`, which is `1`, `-1`, `0` according to whether the reduction is split
multiplicative, nonsplit multiplicative, or additive. -/
