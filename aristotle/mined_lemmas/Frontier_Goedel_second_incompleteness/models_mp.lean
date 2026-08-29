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

theorem models_mp {a b : L.Sentence} (h₁ : T ⊨ᵇ (a ⟹ b)) (h₂ : T ⊨ᵇ a) : T ⊨ᵇ b := by
  rw [Theory.models_sentence_iff] at h₁ h₂ ⊢
  intro M
  have hab := h₁ M
  have ha := h₂ M
  simp only [Sentence.Realize, Formula.Realize, BoundedFormula.realize_imp] at *
  exact hab ha

/-- Entailment of first-order sentences contains the axiom scheme `a → (b → a)`. -/
