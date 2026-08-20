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

theorem bsd_of_finite_mordellWeil {W : WeierstrassCurve ℤ} {L : ℂ → ℂ}
    [Finite (MordellWeil W)] (hL : IsHasseWeilLFunction W L) (h1 : L 1 ≠ 0) :
    BSD W L :=
  (bsd_iff_L_ne_zero_of_rank_zero hL (algebraicRank_eq_zero_of_finite W)).2 h1

/-!
## Main statement
-/

/-- **The Birch and Swinnerton-Dyer statement.**

For an elliptic curve `E/ℚ` given by a global minimal Weierstrass model `W` over `ℤ`, the
Birch–Swinnerton-Dyer conjecture asserts

  `ord_{s=1} L(E, s) = rank E(ℚ)`,

where `L(E, s)` is the entire continuation of the Hasse–Weil `L`-series
`∏_p (1 - a_p p^{-s} + ε_p p^{1-2s})^{-1}` and `rank E(ℚ) = dim_ℚ (ℚ ⊗_ℤ E(ℚ))`.

This theorem records the statement together with the following Lean-checked reductions:

1. the `L`-function of `E` is *unique*, so the conjecture `BSD W L` does not depend on which
   analytic continuation is chosen — in particular `ord_{s=1} L(E,s)` is well defined;
2. `BSD` is equivalent to the local factorization `L(s) = (s-1)^{rank} g(s)` with `g` analytic and
   `g(1) ≠ 0` near `s = 1`;
3. in the rank-zero case BSD reduces to the nonvanishing statement `L(E, 1) ≠ 0`;
4. base case: if the Mordell–Weil group `E(ℚ)` is a torsion group (in particular if it is finite,
   so that the rank is `0`), then `L(E,1) ≠ 0` already implies BSD for `E`. -/
