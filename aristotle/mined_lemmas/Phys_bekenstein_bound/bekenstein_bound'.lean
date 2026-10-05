import Mathlib
/-!
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- NOTE: Lean 4 requires `import` lines to precede every other command in a file,
-- including module doc comments, so the single `import Mathlib` line above is the
-- only thing preceding the requested header comment.

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

/-- The Bekenstein entropy bound `2 π k R E / (ℏ c)` for a system of radius `R`
and total energy `E`, with Boltzmann constant `k`, reduced Planck constant `ℏ`
and speed of light `c`. -/

theorem bekenstein_bound' (k hbar c G S R E A₀ A₁ : ℝ)
    (hhbar : 0 < hbar) (hc : 0 < c) (hG : 0 < G)
    (harea : A₁ = A₀ + 8 * Real.pi * G * E * R / c ^ 4)
    (hGSL : S + k * c ^ 3 * A₀ / (4 * G * hbar) ≤ k * c ^ 3 * A₁ / (4 * G * hbar)) :
    S ≤ 2 * Real.pi * k * R * E / (hbar * c) :=
  bekenstein_bound k hbar c G S R E A₀ A₁ hhbar hc hG harea hGSL

end Phys

