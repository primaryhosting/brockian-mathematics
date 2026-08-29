/-!
# Cantor Powerset
Category: Computer Science
Target: CS.cantor_powerset
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- This file deliberately has no `import` line, since the required header comment above must be
-- the very first thing in the file and Lean requires imports to precede every other command.
-- Everything used below (`Function.Surjective`) is available in the Lean 4 core prelude.
-- The powerset `𝒫(A)` is represented by its characteristic predicates, `A → Prop`, which is
-- exactly (and definitionally) Mathlib's `Set A`.
-- A `Set`-based restatement using Mathlib is given in `RequestProject/CSSet.lean`, where it is
-- also compared with Mathlib's own `Function.cantor_surjective`.

namespace CS

/-- **Cantor's theorem**: there is no surjection from a type `A` onto its powerset
`𝒫(A) = A → Prop`.

Diagonal argument: the "set" `D = fun a => ¬ f a a` is not in the range of `f`, since
`f a = D` would give `f a a ↔ ¬ f a a`. -/
theorem cantor_powerset {A : Type u} (f : A → (A → Prop)) : ¬ Function.Surjective f := by
  intro hf
  obtain ⟨a, ha⟩ := hf (fun x => ¬ f x x)
  have h : f a a ↔ ¬ f a a := congrFun ha a ▸ Iff.rfl
  exact (fun hn => hn (h.mpr hn)) (fun hp => h.mp hp hp)

end CS

import Mathlib
import RequestProject.CS

/-!
# Cantor Powerset, `Set`-valued restatement

`RequestProject/CS.lean` proves `CS.cantor_powerset`, stated for the powerset presented as
characteristic predicates `A → Prop`. Since Mathlib's `Set A` is by definition `A → Prop`, the
statement transfers verbatim; Mathlib itself contains this result as
`Function.cantor_surjective`.
-/

namespace CS

/-- **Cantor's theorem**, `Set`-valued form: no `f : A → Set A` is surjective.
This is `CS.cantor_powerset` transported along `Set A = (A → Prop)`; Mathlib's version of the
same statement is `Function.cantor_surjective`. -/
theorem cantor_powerset_set {A : Type u} (f : A → Set A) : ¬ Function.Surjective f :=
  CS.cantor_powerset f

example {A : Type u} (f : A → Set A) : ¬ Function.Surjective f :=
  Function.cantor_surjective f

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

