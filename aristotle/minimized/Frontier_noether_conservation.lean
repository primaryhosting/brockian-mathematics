/-
# Noether Conservation
Category: Frontier Physics
Target: Frontier.noether_conservation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring `/-! ... -/`, so the
-- header above is written as a plain block comment with identical content.)

import Mathlib

namespace Frontier

/--
**Noether's theorem, one-dimensional case.**

Setting: a Lagrangian `L : ℝ → ℝ → ℝ`, written `L q v`, described through its two partial
derivatives `Lq` (derivative in the position slot) and `Lv` (derivative in the velocity slot).

* `q : ℝ → ℝ` is a trajectory with velocity `q'`.
* `X : ℝ → ℝ` is the infinitesimal generator of a smooth one-parameter symmetry
  `q ↦ q + s • X q`, with derivative `Xd`.
* `hEL` is the Euler–Lagrange equation `d/dt (∂L/∂v) = ∂L/∂q` along the trajectory.
* `hsym` is infinitesimal invariance of the Lagrangian under the symmetry: the first
  variation `(∂L/∂q) · X + (∂L/∂v) · (X' · v)` vanishes identically.

Conclusion: the Noether current `J t = (∂L/∂v)(q t, q' t) · X (q t)` is conserved,
i.e. it takes the same value at any two times.
-/

theorem noether_conservation
    (Lq Lv : ℝ → ℝ → ℝ) (X Xd q q' : ℝ → ℝ)
    (hq : ∀ t, HasDerivAt q (q' t) t)
    (hX : ∀ x, HasDerivAt X (Xd x) x)
    (hEL : ∀ t, HasDerivAt (fun s => Lv (q s) (q' s)) (Lq (q t) (q' t)) t)
    (hsym : ∀ x v, Lq x v * X x + Lv x v * (Xd x * v) = 0) :
    ∀ t₁ t₂, Lv (q t₁) (q' t₁) * X (q t₁) = Lv (q t₂) (q' t₂) * X (q t₂) := by
  -- The Noether current has vanishing derivative: differentiate the product, use the
  -- Euler–Lagrange equation on the first factor and the chain rule on the second,
  -- then invoke infinitesimal invariance.
  have hJ : ∀ t, HasDerivAt (fun s => Lv (q s) (q' s) * X (q s)) 0 t := by
    intro t
    have h := (hEL t).mul ((hX (q t)).comp t (hq t))
    simp only [Pi.mul_def, Function.comp_apply, Function.comp_def] at h
    rwa [hsym (q t) (q' t)] at h
  -- A function on `ℝ` with everywhere vanishing derivative is constant.
  exact fun t₁ t₂ =>
    is_const_of_deriv_eq_zero (fun t => (hJ t).differentiableAt) (fun t => (hJ t).deriv) t₁ t₂

/--
Special case (cyclic coordinate): if the Lagrangian does not depend on the position,
the Euler–Lagrange equation says that the conjugate momentum `p = ∂L/∂v` has vanishing
time derivative, hence is conserved.
-/
