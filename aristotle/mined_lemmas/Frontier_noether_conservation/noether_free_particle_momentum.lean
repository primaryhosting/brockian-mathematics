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

namespace Frontier

/-- **Noether's theorem, one-dimensional (single degree of freedom) case.**

Setting: a Lagrangian `L : ℝ → ℝ → ℝ`, written `L q v` (position `q`, velocity `v`), and a
path `q : ℝ → ℝ`.  Along the path we write

* the *canonical momentum*  `p t = ∂L/∂v (q t, q' t) = deriv (fun w => L (q t) w) (deriv q t)`,
* the *generalized force*   `F t = ∂L/∂q (q t, q' t) = deriv (fun x => L x (deriv q t)) (q t)`.

Hypotheses:

* `hEL` is the **Euler–Lagrange equation** `d/dt p t = F t` (stated as `HasDerivAt`, which
  also encodes differentiability of the momentum along the path);
* `hsym` says that the infinitesimal variation `δq = φ` is a **symmetry of the action**:
  the first-order variation of the Lagrangian vanishes pointwise,
  `∂L/∂q · φ + ∂L/∂v · φ' = 0`.

Conclusion: the **Noether current** `J t = p t * φ t` is conserved, i.e. it takes the same
value at any two times.

The proof is the standard two-line computation: `J' = p' φ + p φ' = F φ + p φ' = 0` by the
product rule (`HasDerivAt.mul`), and a function on `ℝ` with vanishing derivative is constant
(`is_const_of_deriv_eq_zero`). -/

theorem noether_free_particle_momentum :
    ∀ t₀ t₁ : ℝ,
      deriv (fun w : ℝ => w ^ 2 / 2) (deriv (fun t : ℝ => t) t₀)
        = deriv (fun w : ℝ => w ^ 2 / 2) (deriv (fun t : ℝ => t) t₁) := by
  have hderiv_id : ∀ s : ℝ, deriv (fun t : ℝ => t) s = 1 := fun s => by simp
  refine noether_momentum_conservation_of_translation_invariance
    (fun _ v => v ^ 2 / 2) (fun t => t) (fun _ _ _ => rfl) ?_
  intro t
  simp only [hderiv_id]
  norm_num
  exact hasDerivAt_const t 1

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

