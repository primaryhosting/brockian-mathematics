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

theorem noether_momentum_conservation
    (Lv : ℝ → ℝ → ℝ) (q q' : ℝ → ℝ)
    (hEL : ∀ t, HasDerivAt (fun s => Lv (q s) (q' s)) 0 t) :
    ∀ t₁ t₂, Lv (q t₁) (q' t₁) = Lv (q t₂) (q' t₂) :=
  fun t₁ t₂ =>
    is_const_of_deriv_eq_zero (fun t => (hEL t).differentiableAt) (fun t => (hEL t).deriv) t₁ t₂

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

