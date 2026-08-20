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

noncomputable def diag (H : ℕ → ℕ → Bool) : ℕ →. ℕ :=
  fun n => Nat.rfind fun _ => Part.some (!(H n n))

