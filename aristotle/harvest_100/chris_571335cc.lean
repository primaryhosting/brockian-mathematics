/-!
# Disjunction Split Preserves Semantics
Category: Proof-Carrying Apps
Target: PCA.Isolation.disjunction_split_preserves_semantics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace PCA
namespace Isolation

/-- Propositional constraint language used by the isolation engine's model. -/
inductive Formula (α : Type u) : Type u
  | var : α → Formula α
  | tru : Formula α
  | fls : Formula α
  | neg : Formula α → Formula α
  | conj : Formula α → Formula α → Formula α
  | disj : Formula α → Formula α → Formula α
  | impl : Formula α → Formula α → Formula α

namespace Formula

/-- Semantics of a formula relative to a valuation of the atoms. -/
def eval {α : Type u} (v : α → Prop) : Formula α → Prop
  | .var a => v a
  | .tru => True
  | .fls => False
  | .neg p => ¬ eval v p
  | .conj p q => eval v p ∧ eval v q
  | .disj p q => eval v p ∨ eval v q
  | .impl p q => eval v p → eval v q

@[simp] theorem eval_var {α : Type u} (v : α → Prop) (a : α) :
    eval v (.var a) = v a := rfl

@[simp] theorem eval_tru {α : Type u} (v : α → Prop) :
    eval v (.tru : Formula α) = True := rfl

@[simp] theorem eval_fls {α : Type u} (v : α → Prop) :
    eval v (.fls : Formula α) = False := rfl

@[simp] theorem eval_neg {α : Type u} (v : α → Prop) (p : Formula α) :
    eval v (.neg p) = ¬ eval v p := rfl

@[simp] theorem eval_conj {α : Type u} (v : α → Prop) (p q : Formula α) :
    eval v (.conj p q) = (eval v p ∧ eval v q) := rfl

@[simp] theorem eval_disj {α : Type u} (v : α → Prop) (p q : Formula α) :
    eval v (.disj p q) = (eval v p ∨ eval v q) := rfl

@[simp] theorem eval_impl {α : Type u} (v : α → Prop) (p q : Formula α) :
    eval v (.impl p q) = (eval v p → eval v q) := rfl

end Formula

/-- A proof obligation of the isolation engine: a list of assumptions together with a goal. -/
structure Obligation (α : Type u) : Type u where
  /-- The assumptions (isolation context) under which the goal must hold. -/
  hyps : List (Formula α)
  /-- The formula to be established. -/
  goal : Formula α

namespace Obligation

/-- Semantics of an obligation: under every valuation satisfying all assumptions,
the goal holds. -/
def Valid {α : Type u} (o : Obligation α) : Prop :=
  ∀ v : α → Prop, (∀ f ∈ o.hyps, Formula.eval v f) → Formula.eval v o.goal

/-- Every obligation in a list of obligations is valid. -/
def AllValid {α : Type u} (os : List (Obligation α)) : Prop := ∀ o ∈ os, Valid o

end Obligation

/-- The disjunction split transformation: an obligation whose assumption list is
`pre ++ (p ∨ q) :: post` is replaced by the two obligations obtained by replacing the
disjunction with each disjunct in turn. -/
def disjunctionSplit {α : Type u} (pre post : List (Formula α)) (p q goal : Formula α) :
    List (Obligation α) :=
  [⟨pre ++ p :: post, goal⟩, ⟨pre ++ q :: post, goal⟩]

/-- Assumptions in `pre ++ r :: post` are available whenever every member of that list
is satisfied: the auxiliary transfer lemma used by the split. -/
theorem eval_of_mem_replace {α : Type u} {v : α → Prop} {pre post : List (Formula α)}
    {r s : Formula α} (hs : ∀ f ∈ pre ++ s :: post, Formula.eval v f)
    (hr : Formula.eval v r) : ∀ f ∈ pre ++ r :: post, Formula.eval v f := by
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · exact hs f (List.mem_append.mpr (Or.inl hf))
  · rcases List.mem_cons.mp hf with hf | hf
    · exact hf ▸ hr
    · exact hs f (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hf)))

/-- **Disjunction split preserves semantics.**

Splitting a disjunctive assumption of a proof obligation into the two corresponding
obligations is both sound and complete: the original obligation is valid if and only if
both resulting obligations are valid. -/
theorem disjunction_split_preserves_semantics {α : Type u}
    (pre post : List (Formula α)) (p q goal : Formula α) :
    Obligation.Valid ⟨pre ++ Formula.disj p q :: post, goal⟩ ↔
      Obligation.AllValid (disjunctionSplit pre post p q goal) := by
  constructor
  · -- Soundness: each split obligation follows from the original one.
    intro h o ho
    rcases List.mem_cons.mp ho with rfl | ho
    · intro v hv
      refine h v (eval_of_mem_replace hv ?_)
      exact Or.inl (hv p (List.mem_append.mpr (Or.inr (List.mem_cons_self ..))))
    · rcases List.mem_cons.mp ho with rfl | ho
      · intro v hv
        refine h v (eval_of_mem_replace hv ?_)
        exact Or.inr (hv q (List.mem_append.mpr (Or.inr (List.mem_cons_self ..))))
      · exact absurd ho (List.not_mem_nil)
  · -- Completeness: validity of both split obligations implies the original.
    intro h v hv
    have hp : Obligation.Valid (⟨pre ++ p :: post, goal⟩ : Obligation α) :=
      h _ (List.mem_cons_self ..)
    have hq : Obligation.Valid (⟨pre ++ q :: post, goal⟩ : Obligation α) :=
      h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have hv' : ∀ f ∈ pre ++ Formula.disj p q :: post, Formula.eval v f := hv
    have hdisj : Formula.eval v p ∨ Formula.eval v q :=
      hv' (Formula.disj p q) (List.mem_append.mpr (Or.inr (List.mem_cons_self ..)))
    rcases hdisj with hpv | hqv
    · exact hp v (eval_of_mem_replace hv' hpv)
    · exact hq v (eval_of_mem_replace hv' hqv)

end Isolation
end PCA

import RequestProject.PCAIsolation
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


