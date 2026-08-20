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
