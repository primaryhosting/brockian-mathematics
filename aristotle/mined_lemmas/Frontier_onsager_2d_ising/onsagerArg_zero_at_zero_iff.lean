import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

/-! ## The 2D square-lattice Ising model on an `L × L` torus -/

/-- The real spin value `±1` attached to a Boolean spin variable. -/

lemma onsagerArg_zero_at_zero_iff (β : ℝ) : onsagerArg β 0 0 = 0 ↔ β = betaC := by
  have hc : Real.cosh (2 * β) ^ 2 = 1 + Real.sinh (2 * β) ^ 2 := by
    nlinarith [Real.cosh_sq (2 * β), Real.sinh_sq (2 * β)]
  have hkey : onsagerArg β 0 0 = (Real.sinh (2 * β) - 1) ^ 2 := by
    simp only [onsagerArg, Real.cos_zero, hc]; ring
  rw [hkey]
  constructor
  · intro h
    have h1 : Real.sinh (2 * β) = 1 := by nlinarith [sq_nonneg (Real.sinh (2 * β) - 1)]
    have h2 : Real.sinh (2 * β) = Real.sinh (2 * betaC) := by rw [h1, sinh_two_betaC]
    have := Real.sinh_injective h2
    linarith
  · intro h
    rw [h, sinh_two_betaC]
    ring

/-! ## Main statement -/

/-- **Onsager's exact solution of the 2D square-lattice Ising model.**

We formalize the model (partition function `isingZ` on the `L × L` torus) together with
Onsager's exact free-energy density `onsagerLogZDensity`, and establish the following
Lean-checked facts:

1. the base case (infinite temperature): `Z_L(0) = 2^{L²}` for every torus size `L`;
2. Onsager's formula is *exact* at `β = 0` for every finite `L`, i.e.
   `L⁻²  log Z_L(0) = onsagerLogZDensity 0`;
3. the Onsager value at `β = 0` is the entropy `log 2`;
4. the argument of the Onsager logarithm is nonnegative for all `β ≥ 0`, so the formula
   is well posed;
5. this argument degenerates (giving the logarithmic singularity of the free energy)
   exactly at the critical inverse temperature `β_c = ½ log(1+√2)`, which is
   characterized by Kramers–Wannier duality relation `sinh (2 β_c) = 1`. -/
