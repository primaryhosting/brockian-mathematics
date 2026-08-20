import Mathlib

/-!
# A formal model of the isolation engine

This file develops a small, self-contained formal model of the *isolation engine*
used to split a constraint into independent, disjunction-free branches, and proves
its semantic correctness (soundness and completeness).

* `PCA.Isolation.Formula` — the constraint language: atoms, `⊤`, `⊥`, negation,
  conjunction and disjunction.
* `PCA.Isolation.eval` — its semantics, relative to an interpretation of atoms
  `I : A → E → Prop` over environments `E`.
* `PCA.Isolation.nnf` — the negation-normalisation phase.
* `PCA.Isolation.split` — the disjunction-splitting phase, producing a list of
  branches whose disjunction is equivalent to the input.
* `PCA.Isolation.isolate` — the whole engine: normalise, then split.

The main results are
`PCA.Isolation.disjunction_split_preserves_semantics` (an environment satisfies a
constraint iff it satisfies one of the isolated branches), together with the
soundness/completeness corollaries and the structural guarantee that every branch
produced by the engine is disjunction free.
-/

namespace PCA
namespace Isolation

universe u v

/-- Constraint formulas over an atom type `A`. -/
inductive Formula (A : Type u) where
  | tru : Formula A
  | fls : Formula A
  | atom : A → Formula A
  | neg : Formula A → Formula A
  | and : Formula A → Formula A → Formula A
  | or : Formula A → Formula A → Formula A
  deriving DecidableEq

variable {A : Type u} {E : Type v}

/-- Semantics of a constraint formula, relative to an interpretation `I` of the atoms
over environments of type `E`. -/

theorem isolate_satisfiable_iff (I : A → E → Prop) (f : Formula A) :
    (∃ e : E, eval I f e) ↔ ∃ b ∈ isolate f, ∃ e : E, eval I b e := by
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨b, hb, hbe⟩ := isolate_complete I f e he
    exact ⟨b, hb, e, hbe⟩
  · rintro ⟨b, hb, e, hbe⟩
    exact ⟨e, isolate_sound I f e b hb hbe⟩

end Isolation
end PCA

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

