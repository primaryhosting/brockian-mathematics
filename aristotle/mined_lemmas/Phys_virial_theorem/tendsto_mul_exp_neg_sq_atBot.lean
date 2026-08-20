/-
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Statement: For a bound stationary state, 2⟨T⟩ = ⟨r·∇V⟩ (quantum virial theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory Filter Topology

namespace Phys

/-- **Auxiliary integration-by-parts fact.**  If `f` is everywhere differentiable with
integrable derivative `f'` and `f` tends to `0` at both ends of the real line, then the
integral of `f'` over `ℝ` vanishes. -/

theorem tendsto_mul_exp_neg_sq_atBot :
    Tendsto (fun x : ℝ => x * Real.exp (-x ^ 2)) atBot (𝓝 0) := by
  have h := (tendsto_mul_exp_neg_sq_atTop.neg).comp tendsto_neg_atBot_atTop
  have he : ((fun x : ℝ => -(x * Real.exp (-x ^ 2))) ∘ (fun x : ℝ => -x))
      = fun x : ℝ => x * Real.exp (-x ^ 2) := by
    funext x; simp [Function.comp]
  rw [he] at h
  simpa using h

