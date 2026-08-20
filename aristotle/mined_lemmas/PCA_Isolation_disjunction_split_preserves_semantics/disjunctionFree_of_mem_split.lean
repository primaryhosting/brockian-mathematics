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

theorem disjunctionFree_of_mem_split :
    ∀ {f : Formula A}, IsNNF f → ∀ b ∈ split f, DisjunctionFree b := by
  intro f
  induction f with
  | tru => intro _ b hb; simp only [split, List.mem_singleton] at hb; subst hb; trivial
  | fls => intro _ b hb; simp [split] at hb
  | atom a => intro _ b hb; simp only [split, List.mem_singleton] at hb; subst hb; trivial
  | neg f _ =>
      intro hf b hb
      simp only [split, List.mem_singleton] at hb
      subst hb
      cases f with
      | atom a => trivial
      | tru => exact absurd hf not_false
      | fls => exact absurd hf not_false
      | neg g => exact absurd hf not_false
      | and g h => exact absurd hf not_false
      | or g h => exact absurd hf not_false
  | and f g ihf ihg =>
      rintro ⟨hf, hg⟩ b hb
      simp only [split, List.mem_flatMap, List.mem_map] at hb
      obtain ⟨x, hx, y, hy, rfl⟩ := hb
      exact ⟨ihf hf x hx, ihg hg y hy⟩
  | or f g ihf ihg =>
      rintro ⟨hf, hg⟩ b hb
      simp only [split, List.mem_append] at hb
      rcases hb with hb | hb
      · exact ihf hf b hb
      · exact ihg hg b hb

/-! ### The isolation engine -/

/-- The isolation engine: normalise negations, then split the disjunctions,
producing the list of independent branches of a constraint. -/
