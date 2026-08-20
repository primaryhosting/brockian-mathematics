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

open Finset

namespace Math

/-- A fixed primitive 5-th root of unity in `ℂ`. -/

lemma zeta5_pow_injOn :
    Set.InjOn (fun i : ℕ => Math.zeta5 ^ i) (Finset.Ico 1 5 : Finset ℕ) := by
  intro i hi j hj hij
  simp only [Finset.coe_Ico, Set.mem_Ico] at hi hj
  exact Math.isPrimitiveRoot_zeta5.pow_inj hi.2 hj.2 hij

/-- The primitive 5-th roots of unity are exactly `ζ, ζ², ζ³, ζ⁴` for `ζ = exp(2πi/5)`. -/
