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

namespace RiemannScaffold


theorem zeta_zero_of_riemannXi_zero {s : ℂ} (h : RiemannScaffold.riemannXi s = 0)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) : riemannZeta s = 0 := by
  have hΛ : completedRiemannZeta s = 0 := by
    rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' hs0
      · exact absurd (by linear_combination h'') (sub_ne_zero.mpr hs1)
    · exact h'
  have := riemannZeta_def_of_ne_zero hs0
  rw [this, hΛ, zero_div]

