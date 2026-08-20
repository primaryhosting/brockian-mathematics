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

theorem isLFunction_unique {W : WeierstrassCurve ℤ} {L₁ L₂ : ℂ → ℂ}
    (h₁ : IsLFunction W L₁) (h₂ : IsLFunction W L₂) : L₁ = L₂ := by
  have hmem : (2 : ℂ) ∈ {s : ℂ | 3 / 2 < s.re} := by norm_num
  have hev : L₁ =ᶠ[nhds (2 : ℂ)] L₂ :=
    Filter.eventuallyEq_of_mem (isOpen_halfPlane.mem_nhds hmem)
      (eqOn_halfPlane_of_isLFunction h₁ h₂)
  funext z
  exact h₁.1.eqOn_of_preconnected_of_eventuallyEq h₂.1 isPreconnected_univ (Set.mem_univ 2) hev
    (Set.mem_univ z)

/-- Consequently the order of vanishing at `s = 1` does not depend on the choice of the
analytic continuation. -/
