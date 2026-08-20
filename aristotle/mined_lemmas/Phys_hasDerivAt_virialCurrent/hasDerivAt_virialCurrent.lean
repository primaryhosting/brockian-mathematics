import Mathlib
/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
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

namespace Phys

open MeasureTheory Filter Topology

/-- The auxiliary ("virial current") function
`F x = c * (x * ψ'(x)^2 + ψ(x) * ψ'(x)) - x * (V x - E) * ψ x ^ 2`
attached to a solution of the stationary Schrödinger equation
`-c * ψ'' + V ψ = E ψ` (here `c = ℏ²/2m`). -/

theorem hasDerivAt_virialCurrent (c E : ℝ) (psi dpsi ddpsi V dV : ℝ → ℝ)
    (hpsi : ∀ x, HasDerivAt psi (dpsi x) x)
    (hdpsi : ∀ x, HasDerivAt dpsi (ddpsi x) x)
    (hV : ∀ x, HasDerivAt V (dV x) x)
    (hSch : ∀ x, c * ddpsi x = (V x - E) * psi x) (x : ℝ) :
    HasDerivAt (virialCurrent c E psi dpsi V)
      (2 * c * dpsi x ^ 2 - x * dV x * psi x ^ 2) x := by
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hsq : HasDerivAt (fun y : ℝ => dpsi y ^ 2) (2 * dpsi x * ddpsi x) x := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (hdpsi x).pow 2
  have hpsq : HasDerivAt (fun y : ℝ => psi y ^ 2) (2 * psi x * dpsi x) x := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (hpsi x).pow 2
  have h1 : HasDerivAt (fun y : ℝ => y * dpsi y ^ 2)
      (1 * dpsi x ^ 2 + x * (2 * dpsi x * ddpsi x)) x := hid.mul hsq
  have h2 : HasDerivAt (fun y : ℝ => psi y * dpsi y)
      (dpsi x * dpsi x + psi x * ddpsi x) x := (hpsi x).mul (hdpsi x)
  have h3 : HasDerivAt (fun y : ℝ => y * (V y - E))
      (1 * (V x - E) + x * dV x) x := hid.mul ((hV x).sub_const E)
  have h4 : HasDerivAt (fun y : ℝ => y * (V y - E) * psi y ^ 2)
      ((1 * (V x - E) + x * dV x) * psi x ^ 2
        + x * (V x - E) * (2 * psi x * dpsi x)) x := h3.mul hpsq
  have h5 := ((h1.add h2).const_mul c).sub h4
  simpa only [virialCurrent] using h5.congr_deriv (by
    linear_combination (2 * x * dpsi x + psi x) * hSch x)

/-- **Quantum virial theorem (one dimension).**

Let `psi : ℝ → ℝ` be a (real) bound stationary state of the Schrödinger operator
`H = -(ℏ²/2m) d²/dx² + V`, i.e. `psi` is twice differentiable with derivatives
`dpsi`, `ddpsi` and satisfies `-(ℏ²/2m) * ddpsi + V * psi = E * psi`.
Assume the potential `V` is differentiable with derivative `dV`, that the kinetic
and virial densities are integrable, and that the state is *bound*, in the sense
that the boundary quantities `x·ψ'(x)²`, `ψ(x)·ψ'(x)` and `x·(V x - E)·ψ(x)²`
all vanish at `±∞`.

Then `2⟨T⟩ = ⟨x·V'(x)⟩` (in one dimension `r·∇V = x V'(x)`), where
`⟨T⟩ = ∫ (ℏ²/2m) ψ'(x)² dx` is the expected kinetic energy and
`⟨x V'⟩ = ∫ x V'(x) ψ(x)² dx`.

No normalization of `psi` is needed: the identity holds verbatim for any
solution satisfying the stated decay and integrability assumptions (for a
normalized state, `∫ ψ² = 1`, the two sides are literally `2⟨T⟩` and `⟨r·∇V⟩`).

The proof is the integrated form of the pointwise identity
`(ℏ²/2m · (x ψ'² + ψψ') - x (V - E) ψ²)' = 2 (ℏ²/2m) ψ'² - x V' ψ²`
(`Phys.hasDerivAt_virialCurrent`) combined with the fundamental theorem of calculus
on the whole line, `MeasureTheory.integral_of_hasDerivAt_of_tendsto`. -/
