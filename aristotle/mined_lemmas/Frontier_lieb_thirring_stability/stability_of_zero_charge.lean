import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

open MeasureTheory

/-! ## Basic objects -/

/-- Physical space `ℝ^d`, with its Euclidean structure and Lebesgue measure. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Negative part `t⁻ = max (-t) 0` of a real number. -/

theorem stability_of_zero_charge {N K : ℕ} (Z : Fin K → ℝ) (R : Fin K → Space 3)
    (hZ : ∀ j, Z j = 0) (psi : Config N → ℝ) : 0 ≤ manyBodyEnergy Z R psi := by
  have hpot : ∀ x : Config N, 0 ≤ coulombPotential Z R x := by
    intro x
    unfold coulombPotential
    have h1 : (∑ i : Fin N, ∑ j : Fin K, -(Z j / dist (pos x i) (R j))) = 0 := by simp [hZ]
    have h3 : (∑ j : Fin K, ∑ j' : Fin K,
        if j < j' then Z j * Z j' / dist (R j) (R j') else 0) = 0 := by simp [hZ]
    rw [h1, h3]
    have h2 : (0:ℝ) ≤ ∑ i : Fin N, ∑ i' : Fin N,
        if i < i' then 1 / dist (pos x i) (pos x i') else 0 := by
      refine Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ?_
      split <;> positivity
    linarith
  have hA : (0:ℝ) ≤ ∫ x : Config N, coulombPotential Z R x * (psi x)^2 :=
    integral_nonneg fun x => mul_nonneg (hpot x) (sq_nonneg _)
  have h0 : (0:ℝ) ≤ ∫ x : Config N, ‖gradient psi x‖ ^ 2 :=
    integral_nonneg fun x => by positivity
  unfold manyBodyEnergy
  linarith

/-- Pointwise arithmetic–geometric mean bound `v²/a ≤ (4Z)⁻¹ v²/a² + Z v²`, the elementary
ingredient turning Hardy's inequality into a lower bound on the hydrogenic energy. -/
