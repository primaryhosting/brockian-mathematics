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

theorem eval_split (I : A → E → Prop) (e : E) :
    ∀ f : Formula A, (eval I f e ↔ ∃ b ∈ split f, eval I b e) := by
  intro f
  induction f with
  | tru => simp [split]
  | fls => simp [split]
  | atom a => simp [split]
  | neg f _ => simp [split]
  | and f g ihf ihg =>
      simp only [eval_and, split, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨hf, hg⟩
        obtain ⟨x, hx, hxe⟩ := ihf.1 hf
        obtain ⟨y, hy, hye⟩ := ihg.1 hg
        exact ⟨Formula.and x y, ⟨x, hx, y, hy, rfl⟩, hxe, hye⟩
      · rintro ⟨b, ⟨x, hx, y, hy, rfl⟩, hxe, hye⟩
        exact ⟨ihf.2 ⟨x, hx, hxe⟩, ihg.2 ⟨y, hy, hye⟩⟩
  | or f g ihf ihg =>
      simp only [eval_or, split, List.mem_append]
      constructor
      · rintro (hf | hg)
        · obtain ⟨b, hb, hbe⟩ := ihf.1 hf
          exact ⟨b, Or.inl hb, hbe⟩
        · obtain ⟨b, hb, hbe⟩ := ihg.1 hg
          exact ⟨b, Or.inr hb, hbe⟩
      · rintro ⟨b, hb | hb, hbe⟩
        · exact Or.inl (ihf.2 ⟨b, hb, hbe⟩)
        · exact Or.inr (ihg.2 ⟨b, hb, hbe⟩)

/-- Applied to a formula in negation normal form, splitting produces
disjunction-free branches. -/
