/-!
# Disjunction Split Preserves Semantics
Category: Proof-Carrying Apps
Target: PCA.Isolation.disjunction_split_preserves_semantics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: a Lean module docstring must be the first command in a file, so no
`import` line may precede it.  This development therefore uses only the automatically
available `Init` prelude.  Nothing is lost: the lemmas that close the key step
(`List.mem_append`, `or_and_right`, `exists_or`) are core lemmas that are equally
available in the Mathlib environment.
-/

set_option autoImplicit false

universe u

namespace PCA
namespace Isolation

variable {S : Type u}

/-- Isolation conditions: the guard language of the isolation engine over a state
type `S`.  Atoms are arbitrary predicates on states; the language is closed under
conjunction, disjunction and negation. -/
inductive Cond (S : Type u) where
  | tru : Cond S
  | fls : Cond S
  | atom : (S → Prop) → Cond S
  | and : Cond S → Cond S → Cond S
  | or : Cond S → Cond S → Cond S
  | not : Cond S → Cond S

/-- Semantics of an isolation condition: `Holds c s` says that state `s` satisfies `c`. -/

theorem split_no_or {c b : Cond S} (hb : b ∈ split c) :
    ∀ c₁ c₂ : Cond S, b ≠ .or c₁ c₂ := by
  induction c with
  | or c₁ c₂ ih₁ ih₂ =>
      cases List.mem_append.1 hb with
      | inl h => exact ih₁ h
      | inr h => exact ih₂ h
  | _ =>
      simp only [split, List.mem_singleton] at hb
      subst hb
      intro c₁ c₂
      simp

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

