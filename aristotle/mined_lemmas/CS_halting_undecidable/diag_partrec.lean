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

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- The diagonal partial function: on input `n` it halts (returning `0`) exactly when
`H n n = false`, and diverges otherwise. It is partial recursive whenever `H` is computable. -/

theorem diag_partrec {H : ℕ → ℕ → Bool} (hH : Computable₂ H) : Nat.Partrec (diag H) := by
  refine Partrec.nat_iff.1 (Partrec.rfind ?_)
  exact ((((Primrec.dom_bool (fun b => !b)).to_comp.comp
    (hH.comp Computable.id Computable.id))).comp Computable.fst).partrec

/-- The diagonal function halts on `n` iff `H n n = false`. -/
