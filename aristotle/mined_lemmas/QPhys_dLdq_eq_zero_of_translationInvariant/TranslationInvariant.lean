import Mathlib

/-!
# Noether's theorem in one dimension: translation invariance ⟹ conservation of momentum

We work with a Lagrangian `L : ℝ → ℝ → ℝ`, where `L q v` is the Lagrangian evaluated at
position `q` and velocity `v`.

* The *canonical momentum* along a trajectory `q : ℝ → ℝ` is
  `momentum L q t = ∂L/∂v (q t, q' t)`.
* The *Euler–Lagrange equation* says that the time derivative of the momentum equals
  `∂L/∂q (q t, q' t)`.

If `L` is translation invariant, i.e. `L (x + s) v = L x v` for all `s`, then `∂L/∂q = 0`,
hence the momentum is constant in time.
-/

namespace QPhys

/-- The partial derivative of the Lagrangian with respect to the position variable. -/

def TranslationInvariant (L : ℝ → ℝ → ℝ) : Prop := ∀ s x v, L (x + s) v = L x v

/-- A translation invariant Lagrangian has vanishing partial derivative in the position. -/
