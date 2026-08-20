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

