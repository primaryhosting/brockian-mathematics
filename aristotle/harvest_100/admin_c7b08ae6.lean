/-!
# Cantor Powerset
Category: Computer Science
Target: CS.cantor_powerset
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- The powerset of a type, represented by characteristic predicates:
`S : Powerset A` stands for the subset `{a | S a}` of `A`. -/
def Powerset (A : Type u) : Type u := A → Prop

/-- **Cantor's theorem**: there is no surjection from a type `A` onto its powerset `𝒫(A)`.

The powerset is represented here as `A → Prop` (characteristic predicates), which is
definitionally Mathlib's `Set A`; see `CS.cantor_powerset_set` in
`RequestProject.CantorPowersetSet` for the `Set`-valued restatement, which also cites
Mathlib's own `Function.cantor_surjective`.

Proof: the diagonal subset `{a | ¬ f a a}` is not in the range of `f`. -/
theorem cantor_powerset {A : Type u} (f : A → Powerset A) : ¬ Function.Surjective f := fun hf =>
  match hf (fun x => ¬ f x x) with
  | ⟨a, ha⟩ =>
      have h : f a a = ¬ f a a := congrFun ha a
      have hn : ¬ f a a := fun hm => cast h hm hm
      hn (cast h.symm hn)

end CS

import Mathlib
import RequestProject.CantorPowerset

/-!
# Cantor's theorem, `Set`-valued restatement

`CS.cantor_powerset` (in `RequestProject.CantorPowerset`) is stated for the powerset
represented as `A → Prop`.  Here we restate it for Mathlib's `Set A`, deducing it from
`CS.cantor_powerset`.  Mathlib's own version of this result is `Function.cantor_surjective`.
-/

namespace CS

/-- **Cantor's theorem** for Mathlib's `Set`: no function `A → Set A` is surjective. -/
theorem cantor_powerset_set {A : Type u} (f : A → Set A) : ¬ Function.Surjective f :=
  cantor_powerset (A := A) (fun a => (f a : A → Prop))

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

