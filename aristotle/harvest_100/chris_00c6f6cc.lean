/-
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- **Noether's theorem for spatial translations (1D).**

`L q v` is a Lagrangian depending on position `q` and velocity `v`, with partial
derivatives `Lq` (w.r.t. position) and `Lv` (w.r.t. velocity).

Hypotheses:
* `hLq` : `Lq` really is the partial derivative of `L` in the position variable;
* `htrans` : the Lagrangian is invariant under spatial translations `q ↦ q + s`;
* `hp` : `p` is the canonical momentum along the trajectory `q`, i.e.
  `p t = ∂L/∂v (q t, q̇ t)`;
* `hEL` : the trajectory satisfies the Euler–Lagrange equation
  `d/dt p t = ∂L/∂q (q t, q̇ t)`.

Conclusion: the momentum is conserved, i.e. it takes the same value at any two times. -/
theorem noether_translation
    (L Lq Lv : ℝ → ℝ → ℝ)
    (hLq : ∀ x v, HasDerivAt (fun y => L y v) (Lq x v) x)
    (htrans : ∀ s x v, L (x + s) v = L x v)
    (q p : ℝ → ℝ)
    (hp : ∀ t, p t = Lv (q t) (deriv q t))
    (hEL : ∀ t, HasDerivAt p (Lq (q t) (deriv q t)) t) :
    ∀ t₁ t₂, Lv (q t₁) (deriv q t₁) = Lv (q t₂) (deriv q t₂) := by
  -- Translation invariance makes `L` independent of the position variable.
  have hconst : ∀ x v, L x v = L 0 v := by
    intro x v
    have := htrans x 0 v
    simpa using this
  -- Hence the partial derivative of `L` in the position variable vanishes.
  have hzero : ∀ x v, Lq x v = 0 := by
    intro x v
    have h1 : (fun y => L y v) = fun _ : ℝ => L 0 v := funext fun y => hconst y v
    have h2 : HasDerivAt (fun _ : ℝ => L 0 v) (Lq x v) x := h1 ▸ hLq x v
    exact h2.unique (hasDerivAt_const x (L 0 v))
  -- The Euler–Lagrange equation now says that the momentum has zero derivative.
  have hp0 : ∀ t, HasDerivAt p 0 t := by
    intro t
    simpa [hzero] using hEL t
  have hdiff : Differentiable ℝ p := fun t => (hp0 t).differentiableAt
  have hderiv : ∀ t, deriv p t = 0 := fun t => (hp0 t).deriv
  intro t₁ t₂
  rw [← hp t₁, ← hp t₂]
  exact is_const_of_deriv_eq_zero hdiff hderiv t₁ t₂

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

