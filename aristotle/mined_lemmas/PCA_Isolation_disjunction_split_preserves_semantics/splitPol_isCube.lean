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
