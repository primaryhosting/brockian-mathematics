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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Filter Topology WeierstrassCurve

/-!
## Setup

An elliptic curve over `ℚ` is presented by an integral Weierstrass model `W : WeierstrassCurve ℤ`
with nonvanishing discriminant.  We formalize:

* the *algebraic rank* of `W`, i.e. the rank of the Mordell–Weil group `E(ℚ)`;
* the local data (`a_p`, `ε_p`) and the Euler factors of the Hasse–Weil `L`-function of `W`;
* the predicate `IsHasseWeilLFunction W L` saying that the entire function `L` is the analytic
  continuation of the Hasse–Weil `L`-series of `W`;
* the Birch–Swinnerton-Dyer equality `ord_{s=1} L(E, s) = rank E(ℚ)`.
-/

/-- The Mordell–Weil group `E(ℚ)` of the Weierstrass model `W` over `ℤ`, namely the group of
nonsingular rational points of the base change of `W` to `ℚ`. -/
abbrev MordellWeil (W : WeierstrassCurve ℤ) : Type := (W.baseChange ℚ).toAffine.Point

/-- The *algebraic rank* of `W`, i.e. the rank of the Mordell–Weil group `E(ℚ)`, defined as the
dimension of the `ℚ`-vector space `ℚ ⊗_ℤ E(ℚ)`. -/

theorem bsd_iff_factorization {W : WeierstrassCurve ℤ} {L : ℂ → ℂ}
    (hL : IsHasseWeilLFunction W L) :
    BSD W L ↔ ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧ g 1 ≠ 0 ∧
      ∀ᶠ z in 𝓝 (1 : ℂ), L z = (z - 1) ^ (algebraicRank W) * g z := by
  rw [BSD, analyticRank, (hL.entire 1).analyticOrderAt_eq_natCast]
  constructor
  · rintro ⟨g, hg, hg1, hgL⟩
    exact ⟨g, hg, hg1, hgL.mono fun z hz => by simpa [smul_eq_mul] using hz⟩
  · rintro ⟨g, hg, hg1, hgL⟩
    exact ⟨g, hg, hg1, hgL.mono fun z hz => by simpa [smul_eq_mul] using hz⟩

/-- The rank-zero case of BSD: if the algebraic rank vanishes, BSD is equivalent to the
nonvanishing of `L` at `s = 1`. -/
