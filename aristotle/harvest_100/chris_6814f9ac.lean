/-!
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace QPhys

/-- If a Lagrangian `L q v` is invariant under spatial translations `q ↦ q + s`,
then it does not depend on the position variable at all. -/
lemma lagrangian_indep_of_pos {L : ℝ → ℝ → ℝ}
    (hinv : ∀ s x v, L (x + s) v = L x v) (x v : ℝ) :
    L x v = L 0 v := by
  have h := hinv x 0 v
  simpa using h

/-- Translation invariance forces the "generalized force" `∂L/∂q` to vanish. -/
lemma deriv_pos_eq_zero {L : ℝ → ℝ → ℝ}
    (hinv : ∀ s x v, L (x + s) v = L x v) (x v : ℝ) :
    deriv (fun y => L y v) x = 0 := by
  have hfun : (fun y => L y v) = fun _ : ℝ => L 0 v := by
    funext y
    exact lagrangian_indep_of_pos hinv y v
  rw [hfun, deriv_const]

/-- **Noether's theorem for spatial translations (1D).**

Let `L : ℝ → ℝ → ℝ` be a Lagrangian, written `L q v` in terms of position `q` and
velocity `v`, and let `q : ℝ → ℝ` be a trajectory.  The canonical momentum along the
trajectory is `p t = (∂L/∂v) (q t, q' t)`.

Assume:
* `hinv` : `L` is invariant under translations `q ↦ q + s`;
* `hEL`  : the trajectory satisfies the Euler–Lagrange equation
  `d/dt (∂L/∂v) = (∂L/∂q)` along the trajectory;
* `hdiff`: the momentum is a differentiable function of time.

Then the momentum is conserved: it takes the same value at any two times. -/
theorem noether_translation
    (L : ℝ → ℝ → ℝ) (q : ℝ → ℝ)
    (hinv : ∀ s x v, L (x + s) v = L x v)
    (hdiff : Differentiable ℝ (fun t => deriv (fun v => L (q t) v) (deriv q t)))
    (hEL : ∀ t, deriv (fun t => deriv (fun v => L (q t) v) (deriv q t)) t
        = deriv (fun y => L y (deriv q t)) (q t)) :
    ∀ t₁ t₂, deriv (fun v => L (q t₁) v) (deriv q t₁)
        = deriv (fun v => L (q t₂) v) (deriv q t₂) := by
  intro t₁ t₂
  have hzero : ∀ t, deriv (fun t => deriv (fun v => L (q t) v) (deriv q t)) t = 0 := by
    intro t
    rw [hEL t]
    exact deriv_pos_eq_zero hinv (q t) (deriv q t)
  exact is_const_of_deriv_eq_zero hdiff hzero t₁ t₂

end QPhys

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

