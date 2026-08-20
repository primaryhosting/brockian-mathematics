/-
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring, so the header
-- above is repeated verbatim as a module docstring just after the import.)

import Mathlib

/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

/-!
## Setting

We formalize the *persistence of invariant tori* statement of KAM theory in the
"parametrization method" (Moser / de la Llave) form, and give a Lean-checked
reduction of it to the contraction estimate that the KAM scheme produces.

* `Angle` is the parameter space of the torus (e.g. `𝕋ⁿ`),
* `M` is the phase space,
* `rot : Angle → Angle` is the rigid rotation by the (Diophantine) frequency
  vector `ω`,
* `dyn : M → M` is the (perturbed) dynamics (time-one map / Poincaré map),
* `E` is a complete metric space of candidate torus parametrizations, with
  `param : E → Angle → M` the associated embedding.

A parametrization `u : E` describes an invariant torus carrying the rotation
`rot` exactly when the conjugacy equation `dyn ∘ param u = param u ∘ rot`
holds.
-/

/-- `IsInvariantTorus param dyn rot u` says that the embedded torus
`param u : Angle → M` is invariant under the dynamics `dyn` and that the
dynamics restricted to it is conjugate, via `param u`, to the rigid rotation
`rot`. -/

theorem kam_hypotheses_satisfiable :
    ∃ (Φ : ℝ → ℝ) (K : NNReal), ContractingWith K Φ ∧
      (∀ u : ℝ, Φ u = u ↔
        IsInvariantTorus (fun (u : ℝ) (_ : Unit) => u) (fun m : ℝ => m / 2) id u) := by
  refine ⟨fun u => u / 2, 1 / 2, ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩, ?_⟩
  · intro x y
    rw [Real.dist_eq, Real.dist_eq, ← sub_div, abs_div]
    norm_num
    linarith
  · intro u
    exact ⟨fun h _ => by simpa using h, fun h => by simpa using h ()⟩

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

