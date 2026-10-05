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

def firstOrderFramework (T : L.Theory) (Pr : L.Sentence → L.Sentence)
    (hD1 : ∀ a : L.Sentence, T ⊨ᵇ a → T ⊨ᵇ Pr a)
    (hD2 : ∀ a b : L.Sentence, T ⊨ᵇ (Pr (a ⟹ b) ⟹ (Pr a ⟹ Pr b)))
    (hD3 : ∀ a : L.Sentence, T ⊨ᵇ (Pr a ⟹ Pr (Pr a))) :
    ProvabilityFramework where
  Sent := L.Sentence
  imp a b := a ⟹ b
  bot := ⊥
  box := Pr
  Prov a := T ⊨ᵇ a
  mp h₁ h₂ := models_mp h₁ h₂
  axK := models_axK T
  axS := models_axS T
  D1 {a} h := hD1 a h
  D2 := hD2
  D3 := hD3

/--
**Gödel's second incompleteness theorem, in first-order form.**

Let `T` be a theory in a first-order language `L` and let `Pr` be an internal
provability predicate for `T` (for a recursively axiomatized theory extending
`PA`, `Pr ⌜a⌝` is the arithmetized statement "`a` is provable in `T`")
satisfying the Hilbert–Bernays–Löb derivability conditions `D1`, `D2`, `D3`.
Assume the diagonal lemma provides a sentence `g` with `T ⊨ᵇ g ⇔ ∼(Pr g)`.

If `T` is consistent, then `T` does not prove its own consistency statement
`∼(Pr ⊥)`.
-/
