import Mathlib
/-!
# Goldstone
Category: Frontier Phys
Target: Phys.goldstone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

/-- **Goldstone's theorem** (classical field-theory / mechanical form).

Setting: `V : E → ℝ` is a potential on a real normed space `E`, invariant under a
one-parameter family `g : ℝ → (E ≃L[ℝ] E)` of continuous linear symmetries
(`hinv : ∀ t x, V (g t x) = V x`).  The vacuum `v` minimises `V` (`hmin`).
The symmetry is *spontaneously broken*: the orbit `t ↦ g t v` of the vacuum moves,
i.e. it has a nonzero velocity `w ≠ 0` at `t = 0`.

Conclusion: the mass matrix, i.e. the Hessian `fderiv ℝ (fderiv ℝ V) v` of the potential
at the vacuum, annihilates the nonzero vector `w`.  Thus there is a massless mode
(a Goldstone boson): a nonzero fluctuation direction with vanishing mass term. -/

theorem goldstone_mexicanHat :
    ∃ w : ℂ, w ≠ 0 ∧ fderiv ℝ (fun x => fderiv ℝ mexicanHat x) 1 w = 0 := by
  refine goldstone mexicanHat 1 Complex.I rot
    (contDiff_mexicanHat.differentiable (by norm_num)) ?_ ?_ ?_ ?_ ?_ Complex.I_ne_zero
  · intro x
    have h1 : mexicanHat 1 = 0 := by norm_num [mexicanHat]
    rw [h1]
    simp only [mexicanHat]
    positivity
  · intro t x
    have h2 : ‖(rot t : ℂ → ℂ) x‖ = ‖x‖ := (rotation (Circle.exp t)).norm_map x
    simp only [mexicanHat, h2]
  · exact ((contDiff_mexicanHat.fderiv_right (m := 1) le_rfl).differentiable
      (by norm_num)) 1
  · rw [rot_apply]; norm_num
  · have h : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const Complex.I
    have heq : (fun t : ℝ => (rot t : ℂ → ℂ) 1)
        = fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I) := by
      funext t; rw [rot_apply, mul_one]
    rw [heq]
    simpa using h.cexp

end Phys

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

