/-!
# Disjunction Split Preserves Semantics
Category: Proof-Carrying Apps
Target: PCA.Isolation.disjunction_split_preserves_semantics
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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
def eval (I : A → E → Prop) : Formula A → E → Prop
  | Formula.tru, _ => True
  | Formula.fls, _ => False
  | Formula.atom a, e => I a e
  | Formula.neg f, e => ¬ eval I f e
  | Formula.and f g, e => eval I f e ∧ eval I g e
  | Formula.or f g, e => eval I f e ∨ eval I g e

@[simp] theorem eval_tru (I : A → E → Prop) (e : E) :
    eval I Formula.tru e ↔ True := Iff.rfl

@[simp] theorem eval_fls (I : A → E → Prop) (e : E) :
    eval I Formula.fls e ↔ False := Iff.rfl

@[simp] theorem eval_atom (I : A → E → Prop) (a : A) (e : E) :
    eval I (Formula.atom a) e ↔ I a e := Iff.rfl

@[simp] theorem eval_neg (I : A → E → Prop) (f : Formula A) (e : E) :
    eval I (Formula.neg f) e ↔ ¬ eval I f e := Iff.rfl

@[simp] theorem eval_and (I : A → E → Prop) (f g : Formula A) (e : E) :
    eval I (Formula.and f g) e ↔ eval I f e ∧ eval I g e := Iff.rfl

@[simp] theorem eval_or (I : A → E → Prop) (f g : Formula A) (e : E) :
    eval I (Formula.or f g) e ↔ eval I f e ∨ eval I g e := Iff.rfl

/-! ### Negation normal form -/

/-- `nnf f p` is the negation normal form of `f` (if `p = false`) or of `¬ f`
(if `p = true`): negations are pushed down to the atoms. -/
def nnf : Formula A → Bool → Formula A
  | Formula.tru, false => Formula.tru
  | Formula.tru, true => Formula.fls
  | Formula.fls, false => Formula.fls
  | Formula.fls, true => Formula.tru
  | Formula.atom a, false => Formula.atom a
  | Formula.atom a, true => Formula.neg (Formula.atom a)
  | Formula.neg f, p => nnf f (!p)
  | Formula.and f g, false => Formula.and (nnf f false) (nnf g false)
  | Formula.and f g, true => Formula.or (nnf f true) (nnf g true)
  | Formula.or f g, false => Formula.or (nnf f false) (nnf g false)
  | Formula.or f g, true => Formula.and (nnf f true) (nnf g true)

/-- A formula is in negation normal form when negation only occurs directly in
front of an atom. -/
def IsNNF : Formula A → Prop
  | Formula.tru => True
  | Formula.fls => True
  | Formula.atom _ => True
  | Formula.neg (Formula.atom _) => True
  | Formula.neg _ => False
  | Formula.and f g => IsNNF f ∧ IsNNF g
  | Formula.or f g => IsNNF f ∧ IsNNF g

/-- Normalisation preserves the semantics: `nnf f p` denotes `f` when `p = false`
and `¬ f` when `p = true`. -/
theorem eval_nnf (I : A → E → Prop) (e : E) :
    ∀ (f : Formula A) (p : Bool),
      (eval I (nnf f p) e ↔ (if p then ¬ eval I f e else eval I f e)) := by
  intro f
  induction f with
  | tru => intro p; cases p <;> simp [nnf]
  | fls => intro p; cases p <;> simp [nnf]
  | atom a => intro p; cases p <;> simp [nnf]
  | neg f ih =>
      intro p
      cases p <;> simp [nnf, ih]
  | and f g ihf ihg =>
      intro p
      cases p <;> simp [nnf, ihf, ihg]
      tauto
  | or f g ihf ihg =>
      intro p
      cases p <;> simp [nnf, ihf, ihg]

/-- The normalisation phase indeed produces formulas in negation normal form. -/
theorem isNNF_nnf : ∀ (f : Formula A) (p : Bool), IsNNF (nnf f p) := by
  intro f
  induction f with
  | tru => intro p; cases p <;> trivial
  | fls => intro p; cases p <;> trivial
  | atom a => intro p; cases p <;> trivial
  | neg f ih => intro p; exact ih (!p)
  | and f g ihf ihg => intro p; cases p <;> exact ⟨ihf _, ihg _⟩
  | or f g ihf ihg => intro p; cases p <;> exact ⟨ihf _, ihg _⟩

/-! ### Disjunction splitting -/

/-- A formula is disjunction free when no disjunction occurs in it. -/
def DisjunctionFree : Formula A → Prop
  | Formula.tru => True
  | Formula.fls => True
  | Formula.atom _ => True
  | Formula.neg f => DisjunctionFree f
  | Formula.and f g => DisjunctionFree f ∧ DisjunctionFree g
  | Formula.or _ _ => False

/-- The splitting phase of the isolation engine: it turns a formula into the list of
its conjunctive branches. -/
def split : Formula A → List (Formula A)
  | Formula.tru => [Formula.tru]
  | Formula.fls => []
  | Formula.atom a => [Formula.atom a]
  | Formula.neg f => [Formula.neg f]
  | Formula.and f g => (split f).flatMap fun x => (split g).map fun y => Formula.and x y
  | Formula.or f g => split f ++ split g

/-- Splitting preserves the semantics: a formula holds exactly when one of its
branches holds. -/
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
def isolate (f : Formula A) : List (Formula A) := split (nnf f false)

/-- **Main correctness theorem of the isolation engine.**
An environment satisfies a constraint if and only if it satisfies one of the
branches produced by isolating it: disjunction splitting preserves the semantics. -/
theorem disjunction_split_preserves_semantics
    (I : A → E → Prop) (f : Formula A) (e : E) :
    eval I f e ↔ ∃ b ∈ isolate f, eval I b e := by
  rw [isolate, ← eval_split I e (nnf f false)]
  simpa using (eval_nnf I e f false).symm

/-- Soundness of the isolation engine: every branch entails the original constraint. -/
theorem isolate_sound (I : A → E → Prop) (f : Formula A) (e : E)
    (b : Formula A) (hb : b ∈ isolate f) (h : eval I b e) : eval I f e :=
  (disjunction_split_preserves_semantics I f e).2 ⟨b, hb, h⟩

/-- Completeness of the isolation engine: every model of the constraint is a model of
some branch. -/
theorem isolate_complete (I : A → E → Prop) (f : Formula A) (e : E)
    (h : eval I f e) : ∃ b ∈ isolate f, eval I b e :=
  (disjunction_split_preserves_semantics I f e).1 h

/-- Structural guarantee: every branch produced by the isolation engine is
disjunction free. -/
theorem disjunctionFree_of_mem_isolate (f : Formula A) (b : Formula A)
    (hb : b ∈ isolate f) : DisjunctionFree b :=
  disjunctionFree_of_mem_split (isNNF_nnf f false) b hb

/-- Satisfiability is preserved: the constraint has a model iff some branch has one. -/
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

