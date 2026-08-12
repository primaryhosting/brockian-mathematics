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

namespace QPhys

/-- If a Lagrangian `L (x, v)` is invariant under translations of the position variable,
then its partial derivative with respect to position vanishes identically. -/
theorem partial_pos_eq_zero_of_translation_invariant
    (L : ℝ → ℝ → ℝ) (Lx : ℝ → ℝ → ℝ)
    (hLx : ∀ x v, HasDerivAt (fun y : ℝ => L y v) (Lx x v) x)
    (hinv : ∀ x s v, L (x + s) v = L x v) :
    ∀ x v, Lx x v = 0 := by
  intro x v
  have hconst : (fun y : ℝ => L y v) = fun _ : ℝ => L 0 v := by
    funext y
    have := hinv 0 y v
    simpa using this
  have h0 : HasDerivAt (fun y : ℝ => L y v) 0 x := by
    rw [hconst]
    exact hasDerivAt_const x (L 0 v)
  exact (hLx x v).unique h0

/-- **Noether's theorem for translation invariance in one dimension.**

Let `L : ℝ → ℝ → ℝ` be a Lagrangian, written `L x v` in terms of position `x` and
velocity `v`, with partial derivatives `Lx` (in position) and `Lv` (in velocity),
i.e. `Lx x v = ∂L/∂x` and `Lv x v = ∂L/∂v`.

Assume `L` is invariant under translations of the position: `L (x + s) v = L x v`.

Let `q` be a trajectory with velocity `qd` (`qd t = q' t`) satisfying the
Euler–Lagrange equation
`d/dt (Lv (q t) (qd t)) = Lx (q t) (qd t)`,
and let `p t = Lv (q t) (qd t)` be the canonical momentum.

Then the momentum `p` is conserved: it takes the same value at all times. -/
theorem noether_translation
    (L Lx Lv : ℝ → ℝ → ℝ)
    (hLx : ∀ x v, HasDerivAt (fun y : ℝ => L y v) (Lx x v) x)
    (hLv : ∀ x v, HasDerivAt (fun w : ℝ => L x w) (Lv x v) v)
    (hinv : ∀ x s v, L (x + s) v = L x v)
    (q qd p : ℝ → ℝ)
    (hq : ∀ t, HasDerivAt q (qd t) t)
    (hp : ∀ t, p t = Lv (q t) (qd t))
    (hEL : ∀ t, HasDerivAt (fun s : ℝ => Lv (q s) (qd s)) (Lx (q t) (qd t)) t) :
    ∀ t₁ t₂ : ℝ, p t₁ = p t₂ := by
  have hzero : ∀ x v, Lx x v = 0 :=
    partial_pos_eq_zero_of_translation_invariant L Lx hLx hinv
  have hEL0 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Lv (q s) (qd s)) 0 t := by
    intro t
    have := hEL t
    rwa [hzero (q t) (qd t)] at this
  have hdiff : Differentiable ℝ (fun s : ℝ => Lv (q s) (qd s)) := fun t => (hEL0 t).differentiableAt
  have hderiv : ∀ t : ℝ, deriv (fun s : ℝ => Lv (q s) (qd s)) t = 0 := fun t => (hEL0 t).deriv
  intro t₁ t₂
  rw [hp t₁, hp t₂]
  exact is_const_of_deriv_eq_zero hdiff hderiv t₁ t₂

end QPhys

