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

/-!
# Disjunction Split Preserves Semantics
Category: Proof-Carrying Apps
Target: PCA.Isolation.disjunction_split_preserves_semantics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
## The isolation engine's model

An *isolation engine* for a proof-carrying app takes a constraint (a propositional
formula over abstract atoms, describing e.g. a capability guard) and splits it into
a list of independent, disjunction-free *branches*, each branch being a conjunction
of literals that can be discharged in isolation.

This file formalises that model and proves that the split is *semantics preserving*:
the disjunction of the produced branches is logically equivalent to the original
constraint (soundness: every satisfied branch entails the constraint; completeness:
every model of the constraint satisfies some branch).
-/

namespace PCA.Isolation

universe u
variable {α : Type u}

/-- Propositional constraints of the isolation engine. -/
inductive Formula (α : Type u) where
  | atom : α → Formula α
  | tru : Formula α
  | fls : Formula α
  | neg : Formula α → Formula α
  | conj : Formula α → Formula α → Formula α
  | disj : Formula α → Formula α → Formula α

/-- A literal: an atom, possibly negated. -/
structure Lit (α : Type u) where
  atom : α
  positive : Bool

/-- Semantics of constraints under a valuation `v` of the atoms. -/

theorem split_correct (v : α → Bool) (f : Formula α) :
    (evalF v f = true ↔ ∃ c ∈ split f, evalBranch v c = true) ∧
    (evalF v f = false ↔ ∃ c ∈ splitNeg f, evalBranch v c = true) := by
  induction f with
  | atom a => constructor <;> simp [evalF, split, splitNeg, evalBranch, evalLit]
  | tru => simp [evalF, split, splitNeg, evalBranch]
  | fls => simp [evalF, split, splitNeg, evalBranch]
  | neg p ih => simp [evalF, split, splitNeg, ih.1, ih.2]
  | conj p q ihp ihq =>
      simp only [evalF, split, splitNeg, Bool.and_eq_true, Bool.and_eq_false_iff,
        List.mem_append, List.mem_flatMap, List.mem_map]
      constructor
      · rw [ihp.1, ihq.1]
        constructor
        · rintro ⟨⟨c, hc, hc'⟩, ⟨d, hd, hd'⟩⟩
          exact ⟨c ++ d, ⟨c, hc, d, hd, rfl⟩, by simp [evalBranch_append, hc', hd']⟩
        · rintro ⟨e, ⟨c, hc, d, hd, rfl⟩, he⟩
          rw [evalBranch_append] at he
          simp only [Bool.and_eq_true] at he
          exact ⟨⟨c, hc, he.1⟩, ⟨d, hd, he.2⟩⟩
      · rw [ihp.2, ihq.2]
        constructor
        · rintro (⟨c, hc, hc'⟩ | ⟨c, hc, hc'⟩)
          · exact ⟨c, Or.inl hc, hc'⟩
          · exact ⟨c, Or.inr hc, hc'⟩
        · rintro ⟨c, hc | hc, hc'⟩
          · exact Or.inl ⟨c, hc, hc'⟩
          · exact Or.inr ⟨c, hc, hc'⟩
  | disj p q ihp ihq =>
      simp only [evalF, split, splitNeg, Bool.or_eq_true, Bool.or_eq_false_iff,
        List.mem_append, List.mem_flatMap, List.mem_map]
      constructor
      · rw [ihp.1, ihq.1]
        constructor
        · rintro (⟨c, hc, hc'⟩ | ⟨c, hc, hc'⟩)
          · exact ⟨c, Or.inl hc, hc'⟩
          · exact ⟨c, Or.inr hc, hc'⟩
        · rintro ⟨c, hc | hc, hc'⟩
          · exact Or.inl ⟨c, hc, hc'⟩
          · exact Or.inr ⟨c, hc, hc'⟩
      · rw [ihp.2, ihq.2]
        constructor
        · rintro ⟨⟨c, hc, hc'⟩, ⟨d, hd, hd'⟩⟩
          exact ⟨c ++ d, ⟨c, hc, d, hd, rfl⟩, by simp [evalBranch_append, hc', hd']⟩
        · rintro ⟨e, ⟨c, hc, d, hd, rfl⟩, he⟩
          rw [evalBranch_append] at he
          simp only [Bool.and_eq_true] at he
          exact ⟨⟨c, hc, he.1⟩, ⟨d, hd, he.2⟩⟩

/-- **Completeness of the isolation engine**: every model of the constraint satisfies at
least one of the produced branches. -/
