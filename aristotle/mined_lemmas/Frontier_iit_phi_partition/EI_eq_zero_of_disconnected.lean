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

namespace Frontier

/-! ## Gibbs' inequality (nonnegativity of relative entropy) -/

/-- Gibbs' inequality on a finite index type: the relative entropy (Kullback–Leibler
divergence) of two probability distributions is nonnegative, provided `p` is absolutely
continuous with respect to `q`. -/

theorem EI_eq_zero_of_disconnected (M : System V S) {A : Finset V}
    (hA : M.Disconnected A) (s : V → S) : M.EI A s = 0 := by
  refine Finset.sum_eq_zero fun s' _ => ?_
  rw [M.cutProb_eq_prob_of_disconnected hA s s']
  rcases eq_or_ne (M.prob s s') 0 with h | h
  · simp [h]
  · simp [div_self h]

end System

/-- **Integrated information vanishes for a disconnected system.**

`Φ`, defined as the minimum over all bipartitions `{A, Aᶜ}` of the system of the effective
information `EI` (the relative entropy between the actual next-state distribution and the
distribution obtained after cutting the connections between the two parts), is equal to `0`
whenever the system splits into two non-interacting subsystems. -/
