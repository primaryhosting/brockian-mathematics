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
def evalF (v : α → Bool) : Formula α → Bool
  | .atom a => v a
  | .tru => true
  | .fls => false
  | .neg p => !(evalF v p)
  | .conj p q => evalF v p && evalF v q
  | .disj p q => evalF v p || evalF v q

/-- Semantics of a literal. -/
def evalLit (v : α → Bool) (l : Lit α) : Bool :=
  if l.positive then v l.atom else !(v l.atom)

/-- A *branch* is a conjunction of literals; it holds when all its literals hold. -/
def evalBranch (v : α → Bool) (c : List (Lit α)) : Bool :=
  c.all (evalLit v)

/- `split f` isolates the constraint `f` into a list of disjunction-free branches;
`splitNeg f` does the same for the negation of `f`. -/
mutual
def split : Formula α → List (List (Lit α))
  | .atom a => [[⟨a, true⟩]]
  | .tru => [[]]
  | .fls => []
  | .neg p => splitNeg p
  | .conj p q => (split p).flatMap (fun c => (split q).map (fun d => c ++ d))
  | .disj p q => split p ++ split q
def splitNeg : Formula α → List (List (Lit α))
  | .atom a => [[⟨a, false⟩]]
  | .tru => []
  | .fls => [[]]
  | .neg p => split p
  | .conj p q => splitNeg p ++ splitNeg q
  | .disj p q => (splitNeg p).flatMap (fun c => (splitNeg q).map (fun d => c ++ d))
end

/-- The constraint denoted by a literal. -/
def litFormula (l : Lit α) : Formula α :=
  if l.positive then .atom l.atom else .neg (.atom l.atom)

/-- The constraint denoted by a branch: the conjunction of its literals. -/
def branchFormula (c : List (Lit α)) : Formula α :=
  c.foldr (fun l acc => .conj (litFormula l) acc) .tru

/-- The constraint denoted by a list of branches: their disjunction. -/
def branchesFormula (L : List (List (Lit α))) : Formula α :=
  L.foldr (fun c acc => .disj (branchFormula c) acc) .fls

/-- A constraint is *disjunction-free* when it contains no `disj` node; the branches
produced by the isolation engine are of this shape, so they can be discharged
independently. -/
def DisjFree : Formula α → Prop
  | .atom _ => True
  | .tru => True
  | .fls => True
  | .neg p => DisjFree p
  | .conj p q => DisjFree p ∧ DisjFree q
  | .disj _ _ => False

/-! ### Basic evaluation lemmas -/

theorem evalBranch_append (v : α → Bool) (c d : List (Lit α)) :
    evalBranch v (c ++ d) = (evalBranch v c && evalBranch v d) := by
  simp [evalBranch]

theorem evalF_litFormula (v : α → Bool) (l : Lit α) :
    evalF v (litFormula l) = evalLit v l := by
  cases l with
  | mk a pos => cases pos <;> rfl

theorem evalF_branchFormula (v : α → Bool) (c : List (Lit α)) :
    evalF v (branchFormula c) = evalBranch v c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
      show evalF v (.conj (litFormula l) (branchFormula c)) = _
      rw [evalF, evalF_litFormula, ih, evalBranch, evalBranch, List.all_cons]

theorem evalF_branchesFormula (v : α → Bool) (L : List (List (Lit α))) :
    evalF v (branchesFormula L) = L.any (evalBranch v) := by
  induction L with
  | nil => simp [branchesFormula, evalF]
  | cons c L ih =>
      show evalF v (.disj (branchFormula c) (branchesFormula L)) = _
      rw [evalF, evalF_branchFormula, ih, List.any_cons]

/-! ### Correctness of the split -/

/-- Simultaneous correctness of `split` and `splitNeg`: `split f` enumerates exactly the
models of `f`, and `splitNeg f` exactly the models of the negation of `f`. -/
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
theorem split_complete (v : α → Bool) (f : Formula α) (h : evalF v f = true) :
    ∃ c ∈ split f, evalBranch v c = true :=
  (split_correct v f).1.mp h

/-- **Soundness of the isolation engine**: any valuation satisfying one of the produced
branches is a model of the original constraint. -/
theorem split_sound (v : α → Bool) (f : Formula α) (c : List (Lit α))
    (hc : c ∈ split f) (h : evalBranch v c = true) : evalF v f = true :=
  (split_correct v f).1.mpr ⟨c, hc, h⟩

/-- Every branch produced by the isolation engine denotes a disjunction-free constraint. -/
theorem disjFree_branchFormula (c : List (Lit α)) : DisjFree (branchFormula c) := by
  induction c with
  | nil => trivial
  | cons l c ih =>
      refine ⟨?_, ih⟩
      unfold litFormula
      cases l.positive <;> trivial

/-- **Disjunction split preserves semantics.**

The isolation engine rewrites a constraint `f` into the disjunction of the
disjunction-free branches `split f`, and this rewriting is semantics preserving: for
every valuation of the atoms, the split constraint evaluates exactly as `f` does.
Moreover each branch is itself disjunction-free, so the branches can be discharged
in isolation. -/
theorem disjunction_split_preserves_semantics (f : Formula α) :
    (∀ v : α → Bool, evalF v (branchesFormula (split f)) = evalF v f) ∧
    (∀ c ∈ split f, DisjFree (branchFormula c)) := by
  refine ⟨fun v => ?_, fun c _ => disjFree_branchFormula c⟩
  rw [evalF_branchesFormula]
  refine Bool.eq_iff_iff.mpr ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨c, hc, hc'⟩ := List.any_eq_true.mp h
    exact split_sound v f c hc hc'
  · obtain ⟨c, hc, hc'⟩ := split_complete v f h
    exact List.any_eq_true.mpr ⟨c, hc, hc'⟩

end PCA.Isolation

