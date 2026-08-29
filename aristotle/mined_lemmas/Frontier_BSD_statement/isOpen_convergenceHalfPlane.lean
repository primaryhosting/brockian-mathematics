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

theorem isOpen_convergenceHalfPlane : IsOpen convergenceHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

