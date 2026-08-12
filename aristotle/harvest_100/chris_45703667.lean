import Mathlib

/-!
# A formal model of the isolation engine's constraint language

This file develops a small, self-contained model of the constraint language used by an
*isolation engine*: policies are propositional constraints over abstract atoms, and the
engine works by *splitting disjunctions*, i.e. by rewriting a policy into a finite list of
disjunction-free branches (cubes) whose disjunction is semantically equivalent to the
original policy.

The main result is `PCA.Isolation.disjunction_split_preserves_semantics`, which states
that the disjunction split is both **sound** (every model of a branch is a model of the
policy) and **complete** (every model of the policy is a model of some branch).

Supporting results:

* `PCA.Isolation.split_isCube` — every branch produced by the split is a cube, i.e. a
  conjunction of literals, containing no disjunction (negations are pushed to the atoms).
* `PCA.Isolation.isolated_iff_branches` — an isolation query reduces exactly to the
  finitely many cube-vs-cube queries on the branches.
* `PCA.Isolation.sat_iff_branch_sat` — a policy is satisfiable iff some branch is.
-/

namespace PCA.Isolation

universe u

variable {α : Type u}

/-- Policies of the isolation engine: propositional constraints over abstract atoms. -/
inductive Formula (α : Type u) where
  | atom : α → Formula α
  | tru : Formula α
  | fls : Formula α
  | neg : Formula α → Formula α
  | conj : Formula α → Formula α → Formula α
  | disj : Formula α → Formula α → Formula α
  deriving Repr, DecidableEq

/-- Semantics of a policy relative to a valuation `v` of the atoms. -/
def eval (v : α → Prop) : Formula α → Prop
  | .atom a => v a
  | .tru => True
  | .fls => False
  | .neg f => ¬ eval v f
  | .conj f g => eval v f ∧ eval v g
  | .disj f g => eval v f ∨ eval v g

/-- Semantics under a polarity: `evalPol v true f` is `eval v f`, and `evalPol v false f`
is its negation. Used to state the split correctness for both polarities at once. -/
def evalPol (v : α → Prop) : Bool → Formula α → Prop
  | true, f => eval v f
  | false, f => ¬ eval v f

/-- The polarised disjunction split. `splitPol true f` returns the list of branches whose
disjunction is equivalent to `f`; `splitPol false f` returns the branches whose disjunction
is equivalent to `¬ f`. Negations are pushed to the atoms by flipping the polarity. -/
def splitPol : Bool → Formula α → List (Formula α)
  | true, .atom a => [.atom a]
  | false, .atom a => [.neg (.atom a)]
  | true, .tru => [.tru]
  | false, .tru => []
  | true, .fls => []
  | false, .fls => [.tru]
  | p, .neg f => splitPol (!p) f
  | true, .conj f g =>
      (splitPol true f).flatMap fun x => (splitPol true g).map (Formula.conj x)
  | false, .conj f g => splitPol false f ++ splitPol false g
  | true, .disj f g => splitPol true f ++ splitPol true g
  | false, .disj f g =>
      (splitPol false f).flatMap fun x => (splitPol false g).map (Formula.conj x)

/-- The disjunction split of a policy: the list of branches produced by the engine. -/
def split (f : Formula α) : List (Formula α) := splitPol true f

/-- A literal: an atom or a negated atom. -/
def IsLiteral : Formula α → Prop
  | .atom _ => True
  | .neg (.atom _) => True
  | _ => False

/-- A cube: a (possibly trivial) conjunction of literals. Cubes contain no disjunction. -/
def IsCube : Formula α → Prop
  | .atom _ => True
  | .tru => True
  | .fls => False
  | .neg f => IsLiteral (.neg f)
  | .conj f g => IsCube f ∧ IsCube g
  | .disj _ _ => False

/-- Correctness of the polarised split: for either polarity, the branches produced by
`splitPol` have exactly the models of the (possibly negated) policy. -/
theorem splitPol_spec (v : α → Prop) :
    ∀ (p : Bool) (f : Formula α), evalPol v p f ↔ ∃ b ∈ splitPol p f, eval v b := by
  intro p f
  induction f generalizing p with
  | atom a => cases p <;> simp [splitPol, evalPol, eval]
  | tru => cases p <;> simp [splitPol, evalPol, eval]
  | fls => cases p <;> simp [splitPol, evalPol, eval]
  | neg f ih =>
      cases p
      · have := ih true
        simp only [evalPol, eval, splitPol, Bool.not_false] at *
        rw [not_not]
        exact this
      · have := ih false
        simp only [evalPol, eval, splitPol, Bool.not_true] at *
        exact this
  | conj f g ihf ihg =>
      cases p
      · have hf := ihf false
        have hg := ihg false
        simp only [evalPol, eval, splitPol, List.mem_append] at *
        constructor
        · intro h
          by_cases hA : eval v f
          · have hB : ¬ eval v g := fun hB => h ⟨hA, hB⟩
            obtain ⟨b, hb, hb'⟩ := hg.mp hB
            exact ⟨b, Or.inr hb, hb'⟩
          · obtain ⟨b, hb, hb'⟩ := hf.mp hA
            exact ⟨b, Or.inl hb, hb'⟩
        · rintro ⟨b, hb | hb, hb'⟩ ⟨h1, h2⟩
          · exact hf.mpr ⟨b, hb, hb'⟩ h1
          · exact hg.mpr ⟨b, hb, hb'⟩ h2
      · have hf := ihf true
        have hg := ihg true
        simp only [evalPol, eval, splitPol, List.mem_flatMap, List.mem_map] at *
        constructor
        · rintro ⟨h1, h2⟩
          obtain ⟨b, hb, hb'⟩ := hf.mp h1
          obtain ⟨c, hc, hc'⟩ := hg.mp h2
          exact ⟨Formula.conj b c, ⟨b, hb, c, hc, rfl⟩, hb', hc'⟩
        · rintro ⟨d, ⟨b, hb, c, hc, rfl⟩, hd⟩
          exact ⟨hf.mpr ⟨b, hb, hd.1⟩, hg.mpr ⟨c, hc, hd.2⟩⟩
  | disj f g ihf ihg =>
      cases p
      · have hf := ihf false
        have hg := ihg false
        simp only [evalPol, eval, splitPol, List.mem_flatMap, List.mem_map, not_or] at *
        constructor
        · rintro ⟨h1, h2⟩
          obtain ⟨b, hb, hb'⟩ := hf.mp h1
          obtain ⟨c, hc, hc'⟩ := hg.mp h2
          exact ⟨Formula.conj b c, ⟨b, hb, c, hc, rfl⟩, hb', hc'⟩
        · rintro ⟨d, ⟨b, hb, c, hc, rfl⟩, hd⟩
          exact ⟨hf.mpr ⟨b, hb, hd.1⟩, hg.mpr ⟨c, hc, hd.2⟩⟩
      · have hf := ihf true
        have hg := ihg true
        simp only [evalPol, eval, splitPol, List.mem_append] at *
        constructor
        · rintro (h | h)
          · obtain ⟨b, hb, hb'⟩ := hf.mp h
            exact ⟨b, Or.inl hb, hb'⟩
          · obtain ⟨b, hb, hb'⟩ := hg.mp h
            exact ⟨b, Or.inr hb, hb'⟩
        · rintro ⟨b, hb | hb, hb'⟩
          · exact Or.inl (hf.mpr ⟨b, hb, hb'⟩)
          · exact Or.inr (hg.mpr ⟨b, hb, hb'⟩)

/-- **The disjunction split preserves semantics.** A valuation satisfies a policy if and
only if it satisfies one of the branches produced by the disjunction split: the split is
sound and complete. -/
theorem disjunction_split_preserves_semantics (v : α → Prop) (f : Formula α) :
    eval v f ↔ ∃ b ∈ split f, eval v b :=
  splitPol_spec v true f

/-- Soundness: every model of a branch is a model of the policy. -/
theorem disjunction_split_sound (v : α → Prop) (f b : Formula α) (hb : b ∈ split f)
    (h : eval v b) : eval v f :=
  (disjunction_split_preserves_semantics v f).mpr ⟨b, hb, h⟩

/-- Completeness: every model of the policy is a model of some branch. -/
theorem disjunction_split_complete (v : α → Prop) (f : Formula α) (h : eval v f) :
    ∃ b ∈ split f, eval v b :=
  (disjunction_split_preserves_semantics v f).mp h

/-- Every branch produced by the polarised split is a cube, hence disjunction-free. -/
theorem splitPol_isCube : ∀ (p : Bool) (f : Formula α), ∀ b ∈ splitPol p f, IsCube b := by
  intro p f
  induction f generalizing p with
  | atom a => cases p <;> simp [splitPol, IsCube, IsLiteral]
  | tru => cases p <;> simp [splitPol, IsCube]
  | fls => cases p <;> simp [splitPol, IsCube]
  | neg f ih => cases p <;> simpa [splitPol] using ih _
  | conj f g ihf ihg =>
      cases p
      · intro b hb
        simp only [splitPol, List.mem_append] at hb
        rcases hb with hb | hb
        · exact ihf false b hb
        · exact ihg false b hb
      · intro b hb
        simp only [splitPol, List.mem_flatMap, List.mem_map] at hb
        obtain ⟨x, hx, y, hy, rfl⟩ := hb
        exact ⟨ihf true x hx, ihg true y hy⟩
  | disj f g ihf ihg =>
      cases p
      · intro b hb
        simp only [splitPol, List.mem_flatMap, List.mem_map] at hb
        obtain ⟨x, hx, y, hy, rfl⟩ := hb
        exact ⟨ihf false x hx, ihg false y hy⟩
      · intro b hb
        simp only [splitPol, List.mem_append] at hb
        rcases hb with hb | hb
        · exact ihf true b hb
        · exact ihg true b hb

/-- Every branch of the disjunction split is a cube. -/
theorem split_isCube (f : Formula α) : ∀ b ∈ split f, IsCube b :=
  splitPol_isCube true f

/-- Two policies are *isolated* when no valuation satisfies both. -/
def Isolated (f g : Formula α) : Prop := ∀ v : α → Prop, ¬ (eval v f ∧ eval v g)

/-- The isolation check may be performed branchwise: this is what justifies the engine
reducing an isolation query to finitely many cube-vs-cube queries. -/
theorem isolated_iff_branches (f g : Formula α) :
    Isolated f g ↔ ∀ b ∈ split f, ∀ c ∈ split g, Isolated b c := by
  constructor
  · rintro h b hb c hc v ⟨hbv, hcv⟩
    exact h v ⟨disjunction_split_sound v f b hb hbv, disjunction_split_sound v g c hc hcv⟩
  · rintro h v ⟨hfv, hgv⟩
    obtain ⟨b, hb, hbv⟩ := disjunction_split_complete v f hfv
    obtain ⟨c, hc, hcv⟩ := disjunction_split_complete v g hgv
    exact h b hb c hc v ⟨hbv, hcv⟩

/-- A policy is satisfiable iff some branch of its split is. -/
theorem sat_iff_branch_sat (f : Formula α) :
    (∃ v : α → Prop, eval v f) ↔ ∃ b ∈ split f, ∃ v : α → Prop, eval v b := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨b, hb, hbv⟩ := disjunction_split_complete v f hv
    exact ⟨b, hb, v, hbv⟩
  · rintro ⟨b, hb, v, hbv⟩
    exact ⟨v, disjunction_split_sound v f b hb hbv⟩

section Examples

/-- De Morgan is carried out by the split: the negation of a disjunction of two atoms
splits into the single cube consisting of the two negated atoms. -/
example (a b : ℕ) :
    split (Formula.neg (Formula.disj (Formula.atom a) (Formula.atom b))) =
      [Formula.conj (Formula.neg (Formula.atom a)) (Formula.neg (Formula.atom b))] := rfl

/-- A disjunction of two atoms splits into two branches. -/
example (a b : ℕ) :
    split (Formula.disj (Formula.atom a) (Formula.atom b)) =
      [Formula.atom a, Formula.atom b] := rfl

/-- An atom and its negation are isolated. -/
example (a : ℕ) : Isolated (Formula.atom a) (Formula.neg (Formula.atom a)) := by
  rintro v ⟨h1, h2⟩
  exact h2 h1

end Examples

end PCA.Isolation

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

