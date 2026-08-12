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
def Holds : Cond S → S → Prop
  | .tru, _ => True
  | .fls, _ => False
  | .atom p, s => p s
  | .and c₁ c₂, s => Holds c₁ s ∧ Holds c₂ s
  | .or c₁ c₂, s => Holds c₁ s ∨ Holds c₂ s
  | .not c, s => ¬ Holds c s

@[simp] theorem Holds_tru (s : S) : Holds (.tru : Cond S) s ↔ True := Iff.rfl
@[simp] theorem Holds_fls (s : S) : Holds (.fls : Cond S) s ↔ False := Iff.rfl
@[simp] theorem Holds_atom (p : S → Prop) (s : S) : Holds (.atom p) s ↔ p s := Iff.rfl
@[simp] theorem Holds_and (c₁ c₂ : Cond S) (s : S) :
    Holds (.and c₁ c₂) s ↔ Holds c₁ s ∧ Holds c₂ s := Iff.rfl
@[simp] theorem Holds_or (c₁ c₂ : Cond S) (s : S) :
    Holds (.or c₁ c₂) s ↔ Holds c₁ s ∨ Holds c₂ s := Iff.rfl
@[simp] theorem Holds_not (c : Cond S) (s : S) : Holds (.not c) s ↔ ¬ Holds c s := Iff.rfl

/-- The region (predicate on states) carved out by a condition. -/
def region (c : Cond S) : S → Prop := fun s => Holds c s

@[simp] theorem region_apply {c : Cond S} {s : S} : region c s ↔ Holds c s := Iff.rfl

/-- The disjunction split of the isolation engine: a condition is decomposed into the
list of its top-level disjunctive branches, so that each branch can be analysed in
isolation. -/
def split : Cond S → List (Cond S)
  | .or c₁ c₂ => split c₁ ++ split c₂
  | c => [c]

@[simp] theorem split_or (c₁ c₂ : Cond S) : split (.or c₁ c₂) = split c₁ ++ split c₂ := rfl

/-- The split of a condition is never empty: every condition has at least one branch. -/
theorem split_ne_nil (c : Cond S) : split c ≠ [] := by
  induction c with
  | or c₁ c₂ ih₁ _ =>
      simp only [split_or, ne_eq, List.append_eq_nil_iff, not_and]
      exact fun h => absurd h ih₁
  | _ => simp [split]

/-- **Disjunction split preserves semantics.**

Splitting an isolation condition along its top-level disjunctions is both sound and
complete for the semantics: a state satisfies the original condition exactly when it
satisfies at least one of the branches produced by the split.

The inductive step is the distribution of an existential over a list append, which is
`List.mem_append` combined with `or_and_right` and `exists_or`. -/
theorem disjunction_split_preserves_semantics (c : Cond S) (s : S) :
    Holds c s ↔ ∃ b ∈ split c, Holds b s := by
  induction c with
  | or c₁ c₂ ih₁ ih₂ =>
      simp only [Holds_or, split_or, List.mem_append, or_and_right, exists_or]
      exact or_congr ih₁ ih₂
  | _ => simp [split]

/-- Region form of the theorem: the region isolated by a condition is exactly the union
of the regions isolated by its disjunctive branches. -/
theorem region_eq_union_split (c : Cond S) :
    region c = fun s => ∃ b ∈ split c, region b s := by
  funext s
  exact propext (disjunction_split_preserves_semantics c s)

/-- Soundness direction: every branch of the split refines the original condition. -/
theorem split_sound {c b : Cond S} (hb : b ∈ split c) {s : S} (h : Holds b s) : Holds c s :=
  (disjunction_split_preserves_semantics c s).2 ⟨b, hb, h⟩

/-- Completeness direction: every state satisfying the condition is covered by a branch. -/
theorem split_complete {c : Cond S} {s : S} (h : Holds c s) : ∃ b ∈ split c, Holds b s :=
  (disjunction_split_preserves_semantics c s).1 h

/-- The split contains no disjunctions: it is a genuine decomposition into
disjunction-free branches. -/
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

