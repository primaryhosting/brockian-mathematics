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

theorem exists_isLFunction_and_order_iff {W : WeierstrassCurve ℤ}
    (hex : ∃ L : ℂ → ℂ, IsLFunction W L) :
    (∃ L : ℂ → ℂ, IsLFunction W L ∧ analyticOrderAt L 1 = (mwRank W : ℕ∞)) ↔
      ∀ L : ℂ → ℂ, IsLFunction W L → analyticOrderAt L 1 = (mwRank W : ℕ∞) := by
  constructor
  · rintro ⟨L₀, hL₀, hord⟩ L hL
    rwa [isLFunction_unique hL hL₀]
  · rintro h
    obtain ⟨L, hL⟩ := hex
    exact ⟨L, hL, h L hL⟩

/-- **Derivative characterisation of the order of vanishing.** For an entire `L`,
`ord_{s=1} L = n` if and only if the first `n` derivatives of `L` vanish at `1` and the
`n`-th one does not. -/
