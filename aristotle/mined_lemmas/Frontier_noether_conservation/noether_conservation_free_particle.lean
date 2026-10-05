/-
# Noether Conservation
Category: Frontier Physics
Target: Frontier.noether_conservation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The partial derivative `∂L/∂q` of a one–dimensional Lagrangian
`L : ℝ × ℝ → ℝ` (first slot: position, second slot: velocity). -/

theorem noether_conservation_free_particle :
    (Differentiable ℝ freeL) ∧
    (∀ x, HasDerivAt (fun _ : ℝ => (1 : ℝ)) ((fun _ : ℝ => (0 : ℝ)) x) x) ∧
    (∀ x v : ℝ, HasDerivAt
      (fun s : ℝ => freeL (x + s * (fun _ : ℝ => (1 : ℝ)) x,
        v + s * ((fun _ : ℝ => (0 : ℝ)) x * v))) 0 0) ∧
    (∀ t : ℝ, HasDerivAt (fun t : ℝ => t) ((fun _ : ℝ => (1 : ℝ)) t) t) ∧
    (∀ t : ℝ, HasDerivAt
      (fun s : ℝ => Lvel freeL ((fun t : ℝ => t) s) ((fun _ : ℝ => (1 : ℝ)) s))
      (Lpos freeL ((fun t : ℝ => t) t) ((fun _ : ℝ => (1 : ℝ)) t)) t) ∧
    (∀ t : ℝ, noetherCurrent freeL (fun _ : ℝ => (1 : ℝ)) (fun t : ℝ => t)
      (fun _ : ℝ => (1 : ℝ)) t = 1) := by
  refine ⟨freeL_differentiable, fun x => hasDerivAt_const _ _, ?_, fun t => hasDerivAt_id t,
    ?_, ?_⟩
  · intro x v
    simpa [freeL] using (hasDerivAt_const (0 : ℝ) (v ^ 2 / 2))
  · intro t
    simp only [freeL_Lvel, freeL_Lpos]
    exact hasDerivAt_const t (1 : ℝ)
  · intro t
    simp [noetherCurrent]


end Frontier

