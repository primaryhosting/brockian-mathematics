/-
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

/-- **Vanishing of the generalized force under translation invariance.**

If the Lagrangian `L q v` is invariant under translations of the position variable,
`L (q + a) v = L q v`, and `Lq q v` is its partial derivative with respect to the
position, then this partial derivative vanishes identically. -/
theorem partial_pos_eq_zero_of_translation_invariant
    (L Lq : ℝ → ℝ → ℝ)
    (hinv : ∀ a q v, L (q + a) v = L q v)
    (hLq : ∀ q v, HasDerivAt (fun x => L x v) (Lq q v) q) :
    ∀ q v, Lq q v = 0 := by
  intro q v
  have hconst : (fun x => L x v) = fun _ : ℝ => L 0 v := by
    funext x
    simpa using hinv x 0 v
  have h0 : HasDerivAt (fun x => L x v) 0 q := by
    rw [hconst]
    simpa using hasDerivAt_const q (L 0 v)
  exact (hLq q v).unique h0

/-- **Noether's theorem for spatial translations (1D): conservation of momentum.**

Setting.  A one-dimensional mechanical system with trajectory `q : ℝ → ℝ` and velocity
`v : ℝ → ℝ`, governed by a Lagrangian `L : ℝ → ℝ → ℝ`, `L q v`, whose partial derivatives
with respect to position and velocity are `Lq` and `Lv`.  The canonical momentum along the
trajectory is `p t = Lv (q t) (v t)`.

Hypotheses.
* `hinv`: the Lagrangian is **translation invariant**: `L (x + a) v = L x v` for all `a`.
* `hLq`: `Lq x v` is the partial derivative of `L` in the position variable.
* `hEL`: the **Euler–Lagrange equation** holds along the trajectory:
  `d/dt (Lv (q t) (v t)) = Lq (q t) (v t)`.

Conclusion.  The momentum is conserved: `Lv (q t) (v t) = Lv (q s) (v s)` for all times
`t, s`.  (No relation between `q` and `v` is needed: the argument works for the momentum
as an arbitrary function of time satisfying the Euler–Lagrange equation.) -/
theorem noether_translation
    (L Lq Lv : ℝ → ℝ → ℝ) (q v : ℝ → ℝ)
    (hinv : ∀ a x u, L (x + a) u = L x u)
    (hLq : ∀ x u, HasDerivAt (fun y => L y u) (Lq x u) x)
    (hEL : ∀ t, HasDerivAt (fun s => Lv (q s) (v s)) (Lq (q t) (v t)) t) :
    ∀ t s, Lv (q t) (v t) = Lv (q s) (v s) := by
  have hzero : ∀ t, HasDerivAt (fun s => Lv (q s) (v s)) 0 t := by
    intro t
    simpa [partial_pos_eq_zero_of_translation_invariant L Lq hinv hLq (q t) (v t)] using hEL t
  exact is_const_of_deriv_eq_zero (fun t => (hzero t).differentiableAt)
    (fun t => (hzero t).deriv)

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

