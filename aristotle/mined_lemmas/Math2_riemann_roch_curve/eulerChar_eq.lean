/-
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

set_option grind.warning false

namespace Math2

/-- The degree of a divisor `D` on a curve whose (closed) points are indexed by `P`,
where `degPt p` is the degree of the point `p` (equal to `1` when the base field is
algebraically closed).  A divisor is a finitely supported formal `ℤ`-combination of points. -/

theorem eulerChar_eq
    (hzero : h0 0 = 1) (hgenus : h1 0 = g)
    (hadd : ∀ (D : P →₀ ℤ) (p : P),
      eulerChar h0 h1 (D + Finsupp.single p 1) = eulerChar h0 h1 D + degPt p)
    (D : P →₀ ℤ) :
    eulerChar h0 h1 D = degDiv degPt D + 1 - g := by
  classical
  induction D using Finsupp.induction with
  | zero => simp [eulerChar, hzero, hgenus]
  | single_add p n E _ _ ih =>
      have hcomm : Finsupp.single p n + E = E + Finsupp.single p n := by
        rw [add_comm]
      rw [hcomm, eulerChar_add_single degPt h0 h1 hadd, ih, degDiv_add, degDiv_single]
      ring

/-- **Riemann–Roch for a smooth projective curve.**

`P` indexes the closed points of the curve, a divisor is a finitely supported formal
`ℤ`-combination of points, `degPt p` is the degree of the point `p`, `K` is a canonical
divisor and `g` the genus.  The functions `h0 D = ℓ(D)` and `h1 D` record the dimensions
of `H⁰(O(D))` and `H¹(O(D))`.

The two geometric inputs are supplied as hypotheses:

* `hadd`: additivity of the Euler characteristic `χ = h⁰ - h¹` along a point, i.e. the long
  exact cohomology sequence of `0 → O(D) → O(D + p) → k(p) → 0`;
* `hduality`: Serre duality `h¹(D) = ℓ(K - D)`;

together with the normalisations `ℓ(0) = 1` and `h¹(0) = g` (the definition of the genus).

The conclusion is the Riemann–Roch formula `ℓ(D) - ℓ(K - D) = deg D + 1 - g`. -/
