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

theorem penrose_focal_point {L : ℝ} (J : NullJacobi L) (hL : 0 < L) (htrap : J.drho 0 < 0) :
    L ≤ -J.rho 0 / J.drho 0 := by
  have h0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) L := ⟨le_rfl, hL⟩
  have hpos : 0 < J.rho 0 := J.rho_pos 0 h0
  have htr : (J.toNullCongruence).Trapped := by
    show 2 * J.drho 0 / J.rho 0 < 0
    exact div_neg_of_neg_of_pos (by linarith) hpos
  have h := penrose_singularity J.toNullCongruence htr
  have hne : J.drho 0 ≠ 0 := ne_of_lt htrap
  have hrw : -2 / (2 * J.drho 0 / J.rho 0) = -J.rho 0 / J.drho 0 := by
    field_simp
  calc L ≤ -2 / ((J.toNullCongruence).theta 0) := h
    _ = -J.rho 0 / J.drho 0 := hrw

/-- Concavity bound: if `rho'' ≤ 0` on `[0, ∞)` then `rho` lies below its tangent line at
`0`, `rho t ≤ rho 0 + rho' 0 * t`.  This is the integrated form of the null energy
condition in Jacobi variables. -/
