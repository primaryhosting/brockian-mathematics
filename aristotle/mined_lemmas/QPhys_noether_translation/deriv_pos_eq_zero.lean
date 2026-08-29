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
