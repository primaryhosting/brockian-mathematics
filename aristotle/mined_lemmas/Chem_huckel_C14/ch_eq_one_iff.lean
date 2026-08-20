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

namespace Chem

open Matrix SimpleGraph

/-- The adjacency matrix of the cycle graph `C₁₄`, viewed with vertex set `ZMod 14`
(which is definitionally `Fin 14`). -/

lemma ch_eq_one_iff (x : ZMod 14) : ch x = 1 ↔ x = 0 := by
  constructor
  · intro h
    have hd : (14 : ℕ) ∣ x.val := (zeta_primitive.pow_eq_one_iff_dvd x.val).1 h
    have hlt : x.val < 14 := ZMod.val_lt x
    have hv : x.val = 0 := by
      rcases Nat.eq_zero_or_pos x.val with h0 | h0
      · exact h0
      · exact absurd (Nat.le_of_dvd h0 hd) (by omega)
    exact (ZMod.val_eq_zero x).1 hv
  · rintro rfl; exact ch_zero

