import Mathlib

/-!
# Penrose Singularity
Category: Frontier Physics
Target: Frontier.penrose_singularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede every other command, so the header comment
-- above is placed immediately after the single `import Mathlib` line.)

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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## The analytic core: Raychaudhuri focusing

For a null geodesic congruence with vanishing shear and rotation (as holds for the
generators of the boundary of the causal future of a surface), the Raychaudhuri equation
together with the null energy condition `Ric(k,k) ≥ 0` gives the differential inequality

  `θ' ≤ - θ² / 2`

for the expansion `θ` as a function of the affine parameter. The following theorem is the
exact analytic content of the focusing argument: a solution of this inequality with
`θ 0 < 0` blows up (i.e. cannot be continued) before affine parameter `2 / |θ 0|`.
-/

/-- **Raychaudhuri focusing theorem.**  If `θ` satisfies the null-energy-condition
inequality `θ' ≤ -θ²/2` on `[0, L]` and starts out converging, `θ 0 < 0`, then
`L < 2 / (-θ 0)`.  Equivalently: a congruence with initially negative expansion develops a
focal point within affine parameter `2 / |θ 0|`. -/

noncomputable def modelCongruence : TrappedSurfaceCongruence where
  Gen := Unit
  gen_nonempty := ⟨()⟩
  Extends := fun _ T => T < 1
  theta := fun _ t => 2 / (t - 1)
  dtheta := fun _ t => -2 / (t - 1) ^ 2
  hasDerivAt_theta := by
    rintro ⟨⟩ T hT t ht
    have h : t - 1 ≠ 0 := by
      have := ht.2
      intro h; apply absurd hT; push_neg; nlinarith
    have h1 : HasDerivAt (fun t : ℝ => t - 1) 1 t := (hasDerivAt_id t).sub_const 1
    have h2 := (h1.inv h).const_mul (2 : ℝ)
    have hfun : (fun u : ℝ => 2 * ((fun t : ℝ => t - 1) u)⁻¹) = fun u : ℝ => 2 / (u - 1) := by
      funext u; rw [div_eq_mul_inv]
    rw [show (fun u : ℝ => 2 * (fun t : ℝ => t - 1)⁻¹ u) = fun u : ℝ => 2 / (u - 1) from hfun]
      at h2
    convert h2 using 1
    field_simp
  focusConst := 2
  focusConst_pos := by norm_num
  trapped := by rintro ⟨⟩; norm_num
  nec := by
    rintro ⟨⟩ T hT t ht
    have h : t - 1 ≠ 0 := by
      have := ht.2
      intro h; apply absurd hT; push_neg; nlinarith
    have key : -(2:ℝ) / (t - 1) ^ 2 = -(2 / (t - 1)) ^ 2 / 2 := by
      field_simp
    exact le_of_eq key

example : ¬ NullGeodesicallyComplete modelCongruence := penrose_singularity _

/-- Sharpness: the model congruence does extend to every affine parameter strictly below
the Penrose bound `2 / focusConst = 1`. -/
example (T : ℝ) (hT : T < 2 / modelCongruence.focusConst) : modelCongruence.Extends () T := by
  norm_num [modelCongruence] at hT ⊢
  exact hT

#print axioms Frontier.raychaudhuri_focusing
#print axioms Frontier.penrose_singularity
#print axioms Frontier.penrose_singularity'

end Frontier

