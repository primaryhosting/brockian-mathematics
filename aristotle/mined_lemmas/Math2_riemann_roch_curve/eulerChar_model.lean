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

theorem eulerChar_model (g : ℕ) (D : ℕ →₀ ℤ) :
    eulerChar (mh0 g) (mh1 g) D = degDiv degPt1 D + 1 - g := by
  have hcorr := corr_sub g D
  have hdeg := degDiv_sub_canK g D
  have key : ((degDiv degPt1 D + 1 - g).toNat : ℤ)
      - ((-(degDiv degPt1 D + 1 - (g : ℤ))).toNat : ℤ) = degDiv degPt1 D + 1 - g :=
    Int.toNat_sub_toNat_neg _
  have hneg : degDiv degPt1 (canK g - D) + 1 - (g : ℤ)
      = -(degDiv degPt1 D + 1 - (g : ℤ)) := by omega
  simp only [eulerChar, mh1, mh0, hneg, hcorr, Nat.cast_add]
  omega

