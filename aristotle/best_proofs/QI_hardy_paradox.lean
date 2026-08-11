/-!
# Hardy Paradox
Category: Frontier Qi
Target: QI.hardy_paradox
Statement: Hardy's nonlocality argument: a fraction of runs violate local realism without inequalities.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- This file deliberately has no `import` lines so that the header above is the very first
-- thing in the file; the argument only uses `Bool`, `Fin` and `List` from Lean core.
-- A measure-theoretic (Mathlib) version of the same statement is in
-- `RequestProject/HardyMeasure.lean`.

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace QI

/-- Hardy's four events, in a local hidden-variable (local realistic) model.

A run `l : Λ` records the hidden state of the pair; `A i l` and `B j l` are the
predetermined outcomes (`true`/`false`) of Alice's measurement `i` and Bob's measurement `j`
on that run.  The outcome of each party depends only on that party's own setting: this is
exactly the locality assumption. -/
def hardyEvent {Λ : Type u} (A B : Fin 2 → Λ → Bool) (l : Λ) : Bool := A 0 l && B 0 l

/-- **Hardy's nonlocality argument.**

Consider a local hidden-variable model: a list `runs` of experimental runs, on each of which
the outcomes of *all four* measurements are predetermined by local functions
`A 0, A 1, B 0, B 1 : Λ → Bool`.  Hardy's four conditions are

* a nonzero fraction of the runs have `A 0 = true` and `B 0 = true`;
* no run has `A 0 = true` and `B 1 = false`;
* no run has `A 1 = false` and `B 0 = true`;
* no run has `A 1 = true` and `B 1 = true`.

These are contradictory — no inequality is needed.  Indeed, on any run of the first
(positive-fraction) kind, the second condition forces `B 1 = true`, the third then forces
`A 1 = true`, and the fourth is violated.  Since quantum mechanics predicts states and
measurements satisfying all four conditions (with the first event occurring with strictly
positive probability), local realism fails on a nonzero fraction of runs. -/
theorem hardy_paradox {Λ : Type u} (runs : List Λ) (A B : Fin 2 → Λ → Bool)
    (hpos : 0 < runs.countP (hardyEvent A B))
    (h₁ : runs.countP (fun l => A 0 l && !B 1 l) = 0)
    (h₂ : runs.countP (fun l => !A 1 l && B 0 l) = 0)
    (h₃ : runs.countP (fun l => A 1 l && B 1 l) = 0) :
    False := by
  obtain ⟨l, hl, hHardy⟩ := List.countP_pos_iff.mp hpos
  have ha0 : A 0 l = true := by
    simpa [hardyEvent] using (Bool.and_eq_true _ _ |>.mp hHardy).1
  have hb0 : B 0 l = true := by
    simpa [hardyEvent] using (Bool.and_eq_true _ _ |>.mp hHardy).2
  -- The second Hardy condition forces `B 1 l = true`.
  have hb1 : B 1 l = true := by
    have := List.countP_eq_zero.mp h₁ l hl
    revert this
    cases B 1 l <;> simp [ha0]
  -- The third Hardy condition then forces `A 1 l = true`.
  have ha1 : A 1 l = true := by
    have := List.countP_eq_zero.mp h₂ l hl
    revert this
    cases A 1 l <;> simp [hb0]
  -- This contradicts the fourth Hardy condition.
  have := List.countP_eq_zero.mp h₃ l hl
  simp [ha1, hb1] at this

/-- Single-run (deterministic) form of Hardy's argument: the four Hardy conditions are
already contradictory for one hidden state, once the first one is witnessed. -/
theorem hardy_paradox_run {Λ : Type u} (A B : Fin 2 → Λ → Bool)
    (hpos : ∃ l, A 0 l = true ∧ B 0 l = true)
    (h₁ : ∀ l, ¬(A 0 l = true ∧ B 1 l = false))
    (h₂ : ∀ l, ¬(A 1 l = false ∧ B 0 l = true))
    (h₃ : ∀ l, ¬(A 1 l = true ∧ B 1 l = true)) :
    False := by
  obtain ⟨l, ha0, hb0⟩ := hpos
  have hb1 : B 1 l = true := by
    cases hB : B 1 l
    · exact absurd ⟨ha0, hB⟩ (h₁ l)
    · rfl
  have ha1 : A 1 l = true := by
    cases hA : A 1 l
    · exact absurd ⟨hA, hb0⟩ (h₂ l)
    · rfl
  exact h₃ l ⟨ha1, hb1⟩

end QI

import Mathlib

/-!
# Hardy's paradox, measure-theoretic form

A measure-theoretic companion to `QI.hardy_paradox` (see `RequestProject/Main.lean`):
in any local hidden-variable model equipped with a measure describing the statistical
distribution of runs, Hardy's four conditions are contradictory.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace QI

open MeasureTheory

/-- **Hardy's nonlocality argument, measure-theoretic version.**

`μ` is the distribution of the hidden variable, and `A i, B j : Λ → Bool` are the local,
predetermined outcomes.  If the Hardy event `A 0 = true ∧ B 0 = true` has positive measure
while the three other Hardy events are null, we get a contradiction: the Hardy event is
contained in the union of the three null events. -/
theorem hardy_paradox_measure {Λ : Type u} [MeasurableSpace Λ] (μ : Measure Λ)
    (A B : Fin 2 → Λ → Bool)
    (hpos : 0 < μ {l | A 0 l = true ∧ B 0 l = true})
    (h₁ : μ {l | A 0 l = true ∧ B 1 l = false} = 0)
    (h₂ : μ {l | A 1 l = false ∧ B 0 l = true} = 0)
    (h₃ : μ {l | A 1 l = true ∧ B 1 l = true} = 0) :
    False := by
  have hsub : {l | A 0 l = true ∧ B 0 l = true} ⊆
      ({l | A 0 l = true ∧ B 1 l = false} ∪ {l | A 1 l = false ∧ B 0 l = true}) ∪
        {l | A 1 l = true ∧ B 1 l = true} := by
    rintro l ⟨ha, hb⟩
    by_cases hb1 : B 1 l = true
    · by_cases ha1 : A 1 l = true
      · exact Or.inr ⟨ha1, hb1⟩
      · exact Or.inl (Or.inr ⟨by simpa using ha1, hb⟩)
    · exact Or.inl (Or.inl ⟨ha, by simpa using hb1⟩)
  have hnull : μ (({l | A 0 l = true ∧ B 1 l = false} ∪ {l | A 1 l = false ∧ B 0 l = true}) ∪
      {l | A 1 l = true ∧ B 1 l = true}) = 0 :=
    measure_union_null (measure_union_null h₁ h₂) h₃
  exact absurd (measure_mono_null hsub hnull) hpos.ne'

end QI

