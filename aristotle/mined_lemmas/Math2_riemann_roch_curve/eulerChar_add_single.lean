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

theorem eulerChar_add_single
    (hadd : ∀ (D : P →₀ ℤ) (p : P),
      eulerChar h0 h1 (D + Finsupp.single p 1) = eulerChar h0 h1 D + degPt p)
    (D : P →₀ ℤ) (p : P) (n : ℤ) :
    eulerChar h0 h1 (D + Finsupp.single p n) = eulerChar h0 h1 D + n * degPt p := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
      have hsplit : D + Finsupp.single p ((k : ℤ) + 1)
          = (D + Finsupp.single p (k : ℤ)) + Finsupp.single p 1 := by
        rw [add_assoc, ← Finsupp.single_add]
      rw [hsplit, hadd, ih]
      ring
  | pred k ih =>
      have hsplit : D + Finsupp.single p (-(k : ℤ) - 1)
          = (D + Finsupp.single p (-(k : ℤ))) - Finsupp.single p 1 := by
        rw [add_sub_assoc, ← Finsupp.single_sub]
      rw [hsplit, eulerChar_sub_single degPt h0 h1 hadd, ih]
      ring

/-- **Euler characteristic formula** (the "Riemann" half of Riemann–Roch):
under additivity of `χ` along points and the normalisations `h⁰(0) = 1`, `h¹(0) = g`,
one has `χ(D) = deg D + 1 - g` for every divisor `D`. -/
