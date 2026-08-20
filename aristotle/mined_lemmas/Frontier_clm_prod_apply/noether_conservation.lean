/-
# Noether Conservation
Category: Frontier Physics
Target: Frontier.noether_conservation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- Expansion of a continuous linear functional on `ℝ × ℝ` in the standard basis. -/

theorem noether_conservation
    (L : ℝ × ℝ → ℝ) (dL : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ))
    (q v X X' : ℝ → ℝ)
    (hL : ∀ z, HasFDerivAt L (dL z) z)
    (hv : ∀ t, HasDerivAt q (v t) t)
    (hX : ∀ x, HasDerivAt X (X' x) x)
    (hEL : ∀ t, HasDerivAt (fun s => dL (q s, v s) (0, 1)) (dL (q t, v t) (1, 0)) t)
    (hinv : ∀ z : ℝ × ℝ,
      HasDerivAt (fun e : ℝ => L (z.1 + e * X z.1, z.2 + e * (X' z.1 * z.2))) 0 0) :
    ∀ t s : ℝ, dL (q t, v t) (0, 1) * X (q t) = dL (q s, v s) (0, 1) * X (q s) := by
  set J : ℝ → ℝ := fun t => dL (q t, v t) (0, 1) * X (q t) with hJ
  have hJderiv : ∀ t, HasDerivAt J 0 t := by
    intro t
    have hXq : HasDerivAt (fun s => X (q s)) (X' (q t) * v t) t := (hX (q t)).comp t (hv t)
    have hprod := (hEL t).mul hXq
    have hzero : dL (q t, v t) (1, 0) * X (q t)
        + dL (q t, v t) (0, 1) * (X' (q t) * v t) = 0 := by
      have h := dL_apply_generator_eq_zero L dL X X' hL hinv (q t, v t)
      rw [clm_prod_apply] at h
      simpa [mul_comm] using h
    rw [hzero] at hprod
    exact hprod
  intro t s
  exact is_const_of_deriv_eq_zero (fun t => (hJderiv t).differentiableAt)
    (fun t => (hJderiv t).deriv) t s

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

