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

theorem degDiv_canonical
    (hzero : h0 0 = 1) (hgenus : h1 0 = g)
    (hadd : ∀ (D : P →₀ ℤ) (p : P),
      eulerChar h0 h1 (D + Finsupp.single p 1) = eulerChar h0 h1 D + degPt p)
    (hduality : ∀ D : P →₀ ℤ, h1 D = h0 (K - D)) :
    degDiv degPt K = 2 * (g : ℤ) - 2 := by
  have hK := riemann_roch_curve degPt g K h0 h1 hzero hgenus hadd hduality K
  have h0K : h0 K = g := by
    have := hduality 0
    rw [hgenus, sub_zero] at this
    omega
  rw [sub_self] at hK
  rw [h0K, hzero] at hK
  omega

end RiemannRoch

namespace Model

/-!
### A numerical model showing the hypotheses of `riemann_roch_curve` are consistent

For each genus `g` we exhibit divisor data (points, point degrees, a canonical divisor,
and dimension functions `h⁰`, `h¹`) satisfying all the hypotheses of `riemann_roch_curve`.
This shows the hypotheses are not contradictory, so the theorem is not vacuous.
-/

/-- Every point of the model has degree `1`. -/
