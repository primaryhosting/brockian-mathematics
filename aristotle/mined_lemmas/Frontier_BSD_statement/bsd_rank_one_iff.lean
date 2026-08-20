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

theorem bsd_rank_one_iff {W : WeierstrassCurve ℤ} {L : ℂ → ℂ} (hL : IsLFunction W L)
    (h1 : mwRank W = 1) :
    analyticOrderAt L 1 = (mwRank W : ℕ∞) ↔ L 1 = 0 ∧ deriv L 1 ≠ 0 := by
  rw [h1, Nat.cast_one, show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) by norm_cast,
    analyticOrderAt_eq_natCast_iff_iteratedDeriv (hL.1 1 (Set.mem_univ 1))]
  constructor
  · rintro ⟨hz, hd⟩
    refine ⟨?_, ?_⟩
    · simpa using hz 0 Nat.one_pos
    · simpa [iteratedDeriv_one] using hd
  · rintro ⟨hz, hd⟩
    refine ⟨fun i hi => ?_, ?_⟩
    · interval_cases i
      simpa using hz
    · simpa [iteratedDeriv_one] using hd

/-- **The torsion case.** If the Mordell–Weil group `E(ℚ)` is a torsion group, its rank
is `0`. -/
