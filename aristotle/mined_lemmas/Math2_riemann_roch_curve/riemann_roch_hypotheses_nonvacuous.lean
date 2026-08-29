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

theorem riemann_roch_hypotheses_nonvacuous (g : ℕ) :
    ∃ (P : Type) (degPt : P → ℤ) (K : P →₀ ℤ) (h0 h1 : (P →₀ ℤ) → ℕ),
      h0 0 = 1 ∧ h1 0 = g ∧
      (∀ (D : P →₀ ℤ) (p : P),
        eulerChar h0 h1 (D + Finsupp.single p 1) = eulerChar h0 h1 D + degPt p) ∧
      (∀ D : P →₀ ℤ, h1 D = h0 (K - D)) := by
  exact ⟨ℕ, Model.degPt1, Model.canK g, Model.mh0 g, Model.mh1 g, Model.mh0_zero g,
    Model.mh1_zero g, Model.mh_add g, Model.mh_duality g⟩

end Math2

