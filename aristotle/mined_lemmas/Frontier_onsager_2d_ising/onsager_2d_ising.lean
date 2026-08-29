import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Frontier

/-! ## The finite-volume 2D Ising model on an `L × L` torus -/

/-- Shift a periodic (torus) index by one site. -/

theorem onsager_2d_ising :
    -- (1) exact partition function values
    (∀ L : ℕ, ∀ K : ℝ, 0 < isingZ L K) ∧
    (∀ L : ℕ, isingZ L 0 = 2 ^ (L * L)) ∧
    (∀ K : ℝ, isingZ 1 K = 2 * Real.exp (2 * K)) ∧
    -- (2) Onsager's expression at infinite temperature
    onsagerLogZDensity 0 = Real.log 2 ∧
    -- (3) base case: Onsager's formula is exact in every finite volume at K = 0 …
    (∀ L : ℕ, 0 < L → logZDensity L 0 = onsagerLogZDensity 0) ∧
    -- … and therefore the thermodynamic-limit statement holds at K = 0
    OnsagerHoldsAt 0 ∧
    -- (4) structure of Onsager's integrand and the critical coupling
    Real.sinh (2 * criticalCoupling) = 1 ∧
    (∀ K θ φ : ℝ, 0 ≤ K →
      (Real.sinh (2 * K) - 1) ^ 2 ≤
        Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * (Real.cos θ + Real.cos φ)) ∧
    (∀ K θ φ : ℝ, 0 ≤ K → K ≠ criticalCoupling →
      0 < Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * (Real.cos θ + Real.cos φ)) ∧
    -- (5) rigorous free-energy bounds in every finite volume, for every K ≥ 0
    (∀ (L : ℕ) (K : ℝ), 0 < L → 0 ≤ K →
      2 * K ≤ logZDensity L K ∧ logZDensity L K ≤ Real.log 2 + 2 * K) := by
  refine ⟨fun L K => isingZ_pos L K, isingZ_zero, isingZ_one, onsagerLogZDensity_zero,
    fun L hL => ?_, onsagerHoldsAt_zero, sinh_two_criticalCoupling, onsager_arg_lower_bound,
    onsager_arg_pos_of_ne_critical, logZDensity_bounds⟩
  rw [logZDensity_zero L hL, onsagerLogZDensity_zero]

end Frontier

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
set_option pp.piBinderTypes true

set_option grind.warning false

