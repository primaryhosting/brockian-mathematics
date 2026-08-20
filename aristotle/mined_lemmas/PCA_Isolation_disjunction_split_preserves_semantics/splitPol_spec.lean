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
