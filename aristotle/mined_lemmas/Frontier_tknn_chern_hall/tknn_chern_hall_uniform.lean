import Mathlib

/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
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

open MeasureTheory intervalIntegral

/-- The Berry curvature `F = ∂₁A₂ - ∂₂A₁` of a `U(1)` Berry connection `A = (A₁, A₂)`
on the Brillouin zone. -/

theorem tknn_chern_hall_uniform (e h L : ℝ) (n : ℤ) (hL : 0 < L) :
    hallConductance e h (fun _ _ => 0) (fun x _ => 2 * Real.pi * (n : ℝ) * x / L ^ 2) L
      = (n : ℝ) * (e ^ 2 / h) := by
  have hLne : L ≠ 0 := ne_of_gt hL
  refine tknn_chern_hall e h L n hL _ _ (fun _ _ => 0)
    (fun _ _ => 2 * Real.pi * (n : ℝ) / L ^ 2) ?_ ?_ ?_ ?_ ?_ (fun _ => rfl) ?_
  · exact (continuous_const.mul continuous_fst).div_const _
  · exact continuous_const
  · exact continuous_const
  · intro x y
    simpa using ((hasDerivAt_id x).const_mul (2 * Real.pi * (n : ℝ))).div_const (L ^ 2)
  · intro x y
    simpa using (hasDerivAt_const y (0:ℝ))
  · intro y
    field_simp
    ring

end Frontier

