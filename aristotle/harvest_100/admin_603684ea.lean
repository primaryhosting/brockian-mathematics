/-
# Noether Conservation
Category: Frontier Physics
Target: Frontier.noether_conservation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses a plain block comment: Lean 4 requires `import` to precede any
-- module docstring `/-! ... -/`.)

import Mathlib

namespace Frontier

/-!
## Setting

We work with a one-dimensional Lagrangian mechanical system.  The Lagrangian is a
differentiable function `L : ℝ × ℝ → ℝ` of position and velocity, `DL z` denotes its
(Fréchet) derivative at the phase-space point `z = (x, u)`, so that

* `DL z (1, 0)` is the partial derivative `∂L/∂x`,
* `DL z (0, 1)` is the partial derivative `∂L/∂u` (the momentum).

A smooth infinitesimal symmetry is a vector field `X : ℝ → ℝ` on configuration space,
with derivative `X'`.  Its prolongation to phase space is the vector field
`z = (x, u) ↦ (X x, X' x * u)`, and invariance of the action means that `L` is
annihilated by this prolonged field.

Along a trajectory `q` with velocity `v` satisfying the Euler–Lagrange equation
`d/dt (∂L/∂u) = ∂L/∂x`, the Noether current `(∂L/∂u) * X q` is then conserved.
-/

/-- The Noether current attached to a Lagrangian derivative `DL`, a symmetry generator `X`
and a trajectory `t ↦ (q t, v t)`: the momentum contracted with the symmetry generator. -/
noncomputable def noetherCurrent (DL : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ)) (X q v : ℝ → ℝ) (t : ℝ) : ℝ :=
  DL (q t, v t) (0, 1) * X (q t)

/-- Expansion of the directional derivative of the Lagrangian along the prolonged
symmetry vector field in terms of the two partial derivatives. -/
lemma prolonged_apply (DL : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ)) (X X' : ℝ → ℝ) (z : ℝ × ℝ) :
    DL z (X z.1, X' z.1 * z.2)
      = X z.1 * DL z (1, 0) + (X' z.1 * z.2) * DL z (0, 1) := by
  have h : ((X z.1, X' z.1 * z.2) : ℝ × ℝ)
      = X z.1 • ((1, 0) : ℝ × ℝ) + (X' z.1 * z.2) • ((0, 1) : ℝ × ℝ) := by
    simp
  rw [h, map_add, map_smul, map_smul]
  simp [mul_comm]

/-- Infinitesimal invariance of the Lagrangian under the (prolonged) symmetry, expressed as
the vanishing of the `ε`-derivative at `ε = 0` of `ε ↦ L (x + ε X x, u + ε X' x * u)`,
implies the vanishing of the directional derivative `DL z (X x, X' x * u)`. -/
lemma directional_deriv_eq_zero_of_invariant
    (L : ℝ × ℝ → ℝ) (DL : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ))
    (hL : ∀ z, HasFDerivAt L (DL z) z) (X X' : ℝ → ℝ)
    (hinv : ∀ z : ℝ × ℝ,
      HasDerivAt (fun e : ℝ => L (z.1 + e * X z.1, z.2 + e * (X' z.1 * z.2))) 0 0)
    (z : ℝ × ℝ) :
    DL z (X z.1, X' z.1 * z.2) = 0 := by
  have hc : HasDerivAt (fun e : ℝ => ((z.1 + e * X z.1, z.2 + e * (X' z.1 * z.2)) : ℝ × ℝ))
      (X z.1, X' z.1 * z.2) 0 := by
    have h1 : HasDerivAt (fun e : ℝ => z.1 + e * X z.1) (X z.1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (X z.1)).const_add z.1
    have h2 : HasDerivAt (fun e : ℝ => z.2 + e * (X' z.1 * z.2)) (X' z.1 * z.2) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (X' z.1 * z.2)).const_add z.2
    exact h1.prodMk h2
  have hcomp := (hL (z.1 + 0 * X z.1, z.2 + 0 * (X' z.1 * z.2))).comp_hasDerivAt 0 hc
  simp only [zero_mul, add_zero] at hcomp
  exact hcomp.unique (hinv z)

/-- **Key lemma.**  Under the Euler–Lagrange equation and the symmetry (invariance)
condition, the Noether current has vanishing time derivative. -/
lemma hasDerivAt_noetherCurrent_zero
    (DL : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ))
    (X X' q v : ℝ → ℝ)
    (hX : ∀ x, HasDerivAt X (X' x) x)
    (hinv : ∀ z : ℝ × ℝ, DL z (X z.1, X' z.1 * z.2) = 0)
    (hq : ∀ t, HasDerivAt q (v t) t)
    (hEL : ∀ t, HasDerivAt (fun s => DL (q s, v s) (0, 1)) (DL (q t, v t) (1, 0)) t)
    (t : ℝ) :
    HasDerivAt (noetherCurrent DL X q v) 0 t := by
  have hXq : HasDerivAt (fun s => X (q s)) (X' (q t) * v t) t := (hX (q t)).comp t (hq t)
  have h := (hEL t).mul hXq
  have hzero :
      DL (q t, v t) (1, 0) * X (q t) + DL (q t, v t) (0, 1) * (X' (q t) * v t) = 0 := by
    have := hinv (q t, v t)
    rw [prolonged_apply DL X X' (q t, v t)] at this
    simp only at this
    linarith [this]
  simpa [noetherCurrent, hzero] using h

/-- **Noether's theorem (1D case).**  Let `L` be a differentiable Lagrangian on phase
space `ℝ × ℝ` with derivative `DL`, and let `X` be a smooth vector field on configuration
space with derivative `X'` such that `L` is infinitesimally invariant under the flow it
generates, i.e. `ε ↦ L (x + ε * X x, u + ε * (X' x * u))` has vanishing derivative at
`ε = 0` for every phase-space point `(x, u)`.  Then along any trajectory `q` with velocity `v`
solving the Euler–Lagrange equation `d/dt (∂L/∂u) = ∂L/∂x`, the Noether current
`(∂L/∂u) * X q` is conserved: it takes the same value at all times. -/
theorem noether_conservation
    (L : ℝ × ℝ → ℝ) (DL : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ))
    (hL : ∀ z, HasFDerivAt L (DL z) z)
    (X X' q v : ℝ → ℝ)
    (hX : ∀ x, HasDerivAt X (X' x) x)
    (hinv : ∀ z : ℝ × ℝ,
      HasDerivAt (fun e : ℝ => L (z.1 + e * X z.1, z.2 + e * (X' z.1 * z.2))) 0 0)
    (hq : ∀ t, HasDerivAt q (v t) t)
    (hEL : ∀ t, HasDerivAt (fun s => DL (q s, v s) (0, 1)) (DL (q t, v t) (1, 0)) t)
    (t s : ℝ) :
    noetherCurrent DL X q v t = noetherCurrent DL X q v s := by
  have hd := hasDerivAt_noetherCurrent_zero DL X X' q v hX
    (directional_deriv_eq_zero_of_invariant L DL hL X X' hinv) hq hEL
  exact is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt)
    (fun x => (hd x).deriv) t s

/-!
## Non-vacuity

The hypotheses are satisfiable: the free particle `L (x, u) = u ^ 2` is invariant under
spatial translations `X = 1`, and the corresponding conserved current is the momentum,
which is indeed constant along the free motion `q t = a + b * t`.
-/

example (a b : ℝ) :
    ∀ t s : ℝ,
      noetherCurrent (fun z : ℝ × ℝ => (2 * z.2) • (ContinuousLinearMap.snd ℝ ℝ ℝ))
          (fun _ => 1) (fun t => a + b * t) (fun _ => b) t
        = noetherCurrent (fun z : ℝ × ℝ => (2 * z.2) • (ContinuousLinearMap.snd ℝ ℝ ℝ))
          (fun _ => 1) (fun t => a + b * t) (fun _ => b) s := by
  refine noether_conservation (fun z => z.2 ^ 2) _ (fun z => ?_)
    (fun _ => 1) (fun _ => 0) (fun t => a + b * t) (fun _ => b)
    (fun x => hasDerivAt_const x 1) (fun z => ?_)
    (fun t => ?_) (fun t => ?_)
  · have h2 : HasFDerivAt (fun p : ℝ × ℝ => p.2 ^ 2)
        ((2 • z.2 ^ (2 - 1)) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) z :=
      (hasFDerivAt_snd (p := z)).pow 2
    convert h2 using 2
    simp [two_smul]
    ring
  · have hfun : (fun e : ℝ => (z.2 + e * (0 * z.2)) ^ 2) = fun _ : ℝ => z.2 ^ 2 := by
      funext e; ring
    simpa [hfun] using hasDerivAt_const (0 : ℝ) (z.2 ^ 2)
  · simpa using ((hasDerivAt_id t).const_mul b).const_add a
  · simpa using hasDerivAt_const t (2 * b)

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

