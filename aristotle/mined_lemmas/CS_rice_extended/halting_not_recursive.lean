/-
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Statement: The set of indices of a nontrivial semantic property is not recursive (Rice).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib.Computability.Halting

/-!
## Rice's theorem, extended form

We work with `Nat.Partrec.Code`, Mathlib's type of indices (codes) for partial recursive
functions `ℕ →. ℕ`, where `Code.eval : Code → (ℕ →. ℕ)` is the universal evaluation map.

A set `C` of codes is *semantic* if membership depends only on the partial function
computed, and *nontrivial* if it is neither empty nor everything.  Rice's theorem says
that such a `C` is never recursive.

The main theorem `CS.rice_extended` is proved directly from Kleene's recursion (fixed
point) theorem, and we then derive several extended forms: the complement is not
recursive either, the index-set formulation for a property of partial functions, and
the concrete instance that halting on a fixed input is undecidable.
-/

namespace CS

open Nat.Partrec (Code)

/-- A set of codes is *semantic* (extensional) when membership depends only on the
partial function computed by the code, not on the code itself. -/

theorem halting_not_recursive (n : ℕ) :
    ¬ ComputablePred (fun c : Code => (c.eval n).Dom) := by
  obtain ⟨d, hd⟩ := exists_code_diverging
  refine rice_extended_index_set (fun f => (f n).Dom) ⟨Code.const 0, ?_⟩ ⟨d, ?_⟩
  · simp [Nat.Partrec.Code.eval_const]
  · simp [hd]

end CS

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

