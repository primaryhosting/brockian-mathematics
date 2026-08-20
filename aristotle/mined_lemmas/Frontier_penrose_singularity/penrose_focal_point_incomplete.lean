import Mathlib

/-!
# Penrose Singularity
Category: Frontier Physics
Target: Frontier.penrose_singularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-!
## Setting

Mathlib does not (yet) contain Lorentzian causal theory, so the Penrose singularity

theorem penrose_focal_point_incomplete (rho drho ddrho : ℝ → ℝ)
    (hrho : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt rho (drho t) t)
    (hdrho : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt drho (ddrho t) t)
    (hnec : ∀ t ∈ Set.Ici (0 : ℝ), ddrho t ≤ 0)
    (htrap : drho 0 < 0) (hrho0 : 0 < rho 0) :
    ∃ t ∈ Set.Ioc (0 : ℝ) (-rho 0 / drho 0), rho t ≤ 0 := by
  have hcpos : 0 < -rho 0 / drho 0 := div_pos_of_neg_of_neg (by linarith) htrap
  refine ⟨-rho 0 / drho 0, ⟨hcpos, le_rfl⟩, ?_⟩
  have h := rho_le_tangent rho drho ddrho hrho hdrho hnec (-rho 0 / drho 0) hcpos.le
  have hne : drho 0 ≠ 0 := ne_of_lt htrap
  have : rho 0 + drho 0 * (-rho 0 / drho 0) = 0 := by field_simp; ring
  linarith

/-!
## Non-vacuity and sharpness

The hypotheses are satisfiable and the bound is attained: the focusing of the past light
cone of a point in flat space, `rho t = 1 - t` (`rho'' = 0`, i.e. the null energy condition
saturated), is a trapped congruence regular exactly on `[0, 1)`, with
`-rho 0 / rho' 0 = 1`.
-/

/-- The flat-space example `rho t = 1 - t`, a trapped null congruence obeying the null
energy condition and regular exactly on the affine range `[0, 1)`. -/
