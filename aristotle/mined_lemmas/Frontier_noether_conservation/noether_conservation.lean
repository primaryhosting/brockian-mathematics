import Mathlib

/-!
# Noether Conservation
Category: Frontier Physics
Target: Frontier.noether_conservation
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

/-- The partial derivative of a Lagrangian `L : ℝ × ℝ → ℝ` with respect to its first
(position) argument, at the point `z = (q, v)`. -/

theorem noether_conservation
    (L : ℝ × ℝ → ℝ) (X q v : ℝ → ℝ)
    (hq : ∀ t : ℝ, HasDerivAt q (v t) t)
    (hX : ∀ x : ℝ, DifferentiableAt ℝ X x)
    (hEL : ∀ t : ℝ, HasDerivAt (fun s : ℝ => dL_dv L (q s, v s)) (dL_dq L (q t, v t)) t)
    (hsym : ∀ z : ℝ × ℝ, fderiv ℝ L z (X z.1, deriv X z.1 * z.2) = 0) :
    ∀ t₁ t₂ : ℝ, noetherCurrent L X q v t₁ = noetherCurrent L X q v t₂ := by
  have hd : ∀ t : ℝ, HasDerivAt (noetherCurrent L X q v) 0 t :=
    hasDerivAt_noetherCurrent_zero L X q v hq hX hEL hsym
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv)


/-!
### Sanity check: the free particle

`L (q, v) = v * v` is invariant under space translations (generator `X ≡ 1`); the conserved
current is the momentum `2 v`, which is not identically zero.  This witnesses that the
hypotheses of `Frontier.noether_conservation` are satisfiable, i.e. the theorem is not vacuous.
-/

namespace FreeParticle

/-- The free-particle Lagrangian `L (q, v) = v * v`. -/
