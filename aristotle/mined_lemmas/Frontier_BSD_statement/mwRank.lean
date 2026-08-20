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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-!
## The arithmetic side: the Mordell–Weil rank

We work with an integral Weierstrass model `W : WeierstrassCurve ℤ` with nonzero
discriminant; the associated elliptic curve over `ℚ` is the base change
`W.map (Int.castRingHom ℚ)`, whose group of rational points is
`(W.map (Int.castRingHom ℚ)).toAffine.Point` (affine nonsingular points together with
the point at infinity).
-/

/-- The Mordell–Weil group `E(ℚ)` of the integral Weierstrass model `W`. -/
abbrev MordellWeil (W : WeierstrassCurve ℤ) : Type :=
  (W.map (Int.castRingHom ℚ)).toAffine.Point

/-- The Mordell–Weil rank of `E(ℚ)`, defined as the `ℚ`-dimension of `ℚ ⊗_ℤ E(ℚ)`
(equivalently, the rank of the free part of the finitely generated abelian group `E(ℚ)`). -/

noncomputable def mwRank (W : WeierstrassCurve ℤ) : ℕ :=
  Module.finrank ℚ (TensorProduct ℤ ℚ (MordellWeil W))

/-!
## The analytic side: the Hasse–Weil `L`-function
-/

/-- The number of points of the reduction of `W` modulo `p`: the nonsingular affine points
over `ZMod p` together with the point at infinity. -/
