/-
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4.28 requires `import` to precede any module docstring, so the header above is a plain
-- block comment; the identical module docstring is repeated immediately after the imports.)

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
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## The arithmetic side: Mordell–Weil rank

An elliptic curve over `ℚ` is presented by an integral Weierstrass model
`W : WeierstrassCurve ℤ` (a global minimal model, see `Frontier.IsGlobalMinimal`).  Its group of
rational points is the Mordell–Weil group `(W.map (Int.castRingHom ℚ)).toAffine.Point`, and its
rank is the dimension of the `ℚ`-vector space `ℚ ⊗_ℤ E(ℚ)`. -/

/-- The Mordell–Weil group `E(ℚ)` of the elliptic curve defined by the integral Weierstrass
model `W`. -/
abbrev RationalPoints (W : WeierstrassCurve ℤ) : Type :=
  (W.map (Int.castRingHom ℚ)).toAffine.Point

/-- The (algebraic) rank of `E(ℚ)`, defined as `dim_ℚ (ℚ ⊗_ℤ E(ℚ))`.  For a finitely generated
abelian group this is the usual Mordell–Weil rank. -/

noncomputable def analyticRank {W : WeierstrassCurve ℤ} (D : HasseWeilData W) : ℕ∞ :=
  analyticOrderAt D.L 1

/-- **The Birch and Swinnerton-Dyer conjecture** (rank part) for the elliptic curve given by the
global minimal integral Weierstrass model `W`: the Hasse–Weil `L`-function of `E` exists (it
admits an analytic continuation to `s = 1`) and
`ord_{s = 1} L(E, s) = rank E(ℚ)`. -/
