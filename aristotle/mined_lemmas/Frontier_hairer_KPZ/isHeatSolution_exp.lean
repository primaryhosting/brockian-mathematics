import Mathlib

/-!
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` lines to precede any module documentation, so this header comment
appears immediately after the single `import Mathlib` line.)
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## Partial derivatives on space-time `ℝ × ℝ`

A point `p : ℝ × ℝ` is read as `(t, x)` with `t` the time variable and `x` the space variable. -/

/-- Partial derivative in the time variable of a space-time function. -/

theorem isHeatSolution_exp : IsHeatSolution (fun p : ℝ × ℝ => Real.exp (p.1 + p.2)) := by
  have hdx : ∀ p : ℝ × ℝ, dx (fun p : ℝ × ℝ => Real.exp (p.1 + p.2)) p
      = Real.exp (p.1 + p.2) := by
    intro p
    have hd : HasDerivAt (fun y : ℝ => Real.exp (p.1 + y)) (Real.exp (p.1 + p.2)) p.2 := by
      simpa using ((hasDerivAt_id p.2).const_add p.1).exp
    simpa [dx] using hd.deriv
  refine ⟨fun p => Real.exp_pos _, fun t => ?_, fun t => ?_, fun p => ?_, fun p => ?_⟩
  · exact Real.differentiable_exp.comp (differentiable_id.const_add t)
  · simp only [hdx]
    exact Real.differentiable_exp.comp (differentiable_id.const_add t)
  · exact (Real.differentiable_exp.comp (differentiable_id.add_const p.2)).differentiableAt
  · have h1 : dt (fun p : ℝ × ℝ => Real.exp (p.1 + p.2)) p = Real.exp (p.1 + p.2) := by
      have hd : HasDerivAt (fun s : ℝ => Real.exp (s + p.2)) (Real.exp (p.1 + p.2)) p.1 := by
        simpa using ((hasDerivAt_id p.1).add_const p.2).exp
      show deriv (fun s : ℝ => Real.exp (s + p.2)) p.1 = _
      exact hd.deriv
    have h2 : dx (dx (fun p : ℝ × ℝ => Real.exp (p.1 + p.2))) p = Real.exp (p.1 + p.2) := by
      have hfun : (fun y : ℝ => dx (fun p : ℝ × ℝ => Real.exp (p.1 + p.2)) (p.1, y))
          = fun y : ℝ => Real.exp (p.1 + y) := by
        funext y
        simpa using hdx (p.1, y)
      have hd : HasDerivAt (fun y : ℝ => Real.exp (p.1 + y)) (Real.exp (p.1 + p.2)) p.2 := by
        simpa using ((hasDerivAt_id p.2).const_add p.1).exp
      rw [dx, hfun]
      exact hd.deriv
    rw [h1, h2]

/-- The corresponding KPZ solution `h (t, x) = t + x`, obtained from `Frontier.hairer_KPZ`. -/
