/-
First-order instantiation of the abstract second incompleteness theorem
proved in `RequestProject.GoedelSecondIncompleteness`.
-/

import Mathlib
import RequestProject.GoedelSecondIncompleteness

set_option autoImplicit false

namespace Frontier

open FirstOrder Language

variable {L : Language} {T : L.Theory}

/-- Modus ponens for entailment of first-order sentences. -/

theorem models_axS (T : L.Theory) (a b c : L.Sentence) :
    T ⊨ᵇ ((a ⟹ (b ⟹ c)) ⟹ ((a ⟹ b) ⟹ (a ⟹ c))) := by
  rw [Theory.models_sentence_iff]
  intro M
  simp only [Sentence.Realize, Formula.Realize, BoundedFormula.realize_imp]
  tauto

/-- The `ProvabilityFramework` of `L`-sentences over a theory `T`, where `Pr` is an
internal provability predicate satisfying the derivability conditions. -/
