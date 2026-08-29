/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The Lieb–Thirring constant appearing in the kinetic energy inequality that is dual to
the Lieb–Thirring eigenvalue bound with constant `L` (in dimension `3`, exponent `γ = 1`). -/

theorem liebThirring_dual_hypothesis_sharp
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (ρ : α → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (L : ℝ) (hL : 0 < L)
    (hint : Integrable (fun x => (ρ x) ^ ((5 : ℝ) / 3)) μ) :
    ∀ V : α → ℝ, (∀ x, 0 ≤ V x) →
      Integrable (fun x => V x * ρ x) μ →
      Integrable (fun x => (V x) ^ ((5 : ℝ) / 2)) μ →
      (ltKineticConst L * ∫ x, (ρ x) ^ ((5 : ℝ) / 3) ∂μ) - ∫ x, V x * ρ x ∂μ
        ≥ - L * ∫ x, (V x) ^ ((5 : ℝ) / 2) ∂μ := by
  intro V hV hi1 hi2
  have hmono : (∫ x, V x * ρ x ∂μ)
      ≤ ∫ x, (ltKineticConst L * (ρ x) ^ ((5 : ℝ) / 3) + L * (V x) ^ ((5 : ℝ) / 2)) ∂μ := by
    refine integral_mono hi1 ((hint.const_mul _).add (hi2.const_mul _)) (fun x => ?_)
    simpa [mul_comm] using young_liebThirring (L := L) (a := ρ x) (b := V x) hL (hρ x) (hV x)
  rw [integral_add (hint.const_mul _) (hi2.const_mul _), integral_const_mul,
    integral_const_mul] at hmono
  linarith

/-- **Optimality of the constant.** If a constant `K'` works in the kinetic energy
inequality for every state satisfying the variational Lieb–Thirring hypothesis (tested here
on the one-point measure space, where `ρ ≡ 1`), then `K' ≤ K_L`. -/
