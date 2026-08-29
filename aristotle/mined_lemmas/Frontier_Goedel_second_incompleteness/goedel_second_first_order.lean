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

theorem goedel_second_first_order (T : L.Theory) (Pr : L.Sentence → L.Sentence)
    (hD1 : ∀ a : L.Sentence, T ⊨ᵇ a → T ⊨ᵇ Pr a)
    (hD2 : ∀ a b : L.Sentence, T ⊨ᵇ (Pr (a ⟹ b) ⟹ (Pr a ⟹ Pr b)))
    (hD3 : ∀ a : L.Sentence, T ⊨ᵇ (Pr a ⟹ Pr (Pr a)))
    (hdiag : ∃ g : L.Sentence, T ⊨ᵇ (g ⇔ ∼(Pr g)))
    (hcon : ¬ T ⊨ᵇ (⊥ : L.Sentence)) :
    ¬ T ⊨ᵇ ∼(Pr (⊥ : L.Sentence)) := by
  obtain ⟨g, hg⟩ := hdiag
  have hg₁ : T ⊨ᵇ (g ⟹ (Pr g ⟹ ⊥)) := by
    rw [Theory.models_sentence_iff] at hg ⊢
    intro M
    have h := hg M
    simp only [Sentence.Realize, Formula.Realize, BoundedFormula.realize_iff,
      BoundedFormula.realize_imp, BoundedFormula.realize_not,
      BoundedFormula.realize_bot] at *
    tauto
  have hg₂ : T ⊨ᵇ ((Pr g ⟹ ⊥) ⟹ g) := by
    rw [Theory.models_sentence_iff] at hg ⊢
    intro M
    have h := hg M
    simp only [Sentence.Realize, Formula.Realize, BoundedFormula.realize_iff,
      BoundedFormula.realize_imp, BoundedFormula.realize_not,
      BoundedFormula.realize_bot] at *
    tauto
  have hmain :=
    Goedel_second_incompleteness (firstOrderFramework T Pr hD1 hD2 hD3) ⟨g, hg₁, hg₂⟩ hcon
  intro hCon
  refine hmain ?_
  show T ⊨ᵇ (Pr (⊥ : L.Sentence) ⟹ ⊥)
  rw [Theory.models_sentence_iff] at hCon ⊢
  intro M
  have h := hCon M
  simp only [Sentence.Realize, Formula.Realize, BoundedFormula.realize_imp,
    BoundedFormula.realize_not, BoundedFormula.realize_bot] at *
  tauto

end Frontier

/-!
# Goedel Second Incompleteness
Category: Frontier — Set Theory
Target: Frontier.Goedel_second_incompleteness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u

namespace Frontier

/--
`ProvabilityFramework` packages the syntactic data and the *Hilbert–Bernays–Löb
derivability conditions* that any consistent, recursively axiomatized theory `T`
extending `PA` satisfies.

* `Sent` is the type of sentences of the language of `T`;
* `imp` is implication and `bot` is falsum;
* `box a` is the arithmetized statement "`a` is provable in `T`" (this uses that
  `T` is recursively axiomatized, so that provability in `T` is expressible);
* `Prov a` means "`T` proves `a`".

The axioms are:

* `mp` : `Prov` is closed under modus ponens;
* `axK`, `axS` : `T` proves the two standard implicational axiom schemes
  (`T` extends `PA`, hence proves all propositional tautologies; only these two
  schemes are needed below);
* `D1`, `D2`, `D3` : the three derivability conditions
  `⊢ a ⟹ ⊢ □a`, `⊢ □(a → b) → (□a → □b)`, `⊢ □a → □□a`.
-/
structure ProvabilityFramework where
  /-- The type of sentences of the theory. -/
  Sent : Type u
  /-- Implication between sentences. -/
  imp : Sent → Sent → Sent
  /-- The false sentence. -/
  bot : Sent
  /-- The arithmetized provability predicate of the theory. -/
  box : Sent → Sent
  /-- `Prov a` means that the theory proves `a`. -/
  Prov : Sent → Prop
  /-- Provability is closed under modus ponens. -/
  mp : ∀ {a b : Sent}, Prov (imp a b) → Prov a → Prov b
  /-- The axiom scheme `a → (b → a)`. -/
  axK : ∀ a b : Sent, Prov (imp a (imp b a))
  /-- The axiom scheme `(a → (b → c)) → ((a → b) → (a → c))`. -/
  axS : ∀ a b c : Sent,
    Prov (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  /-- First derivability condition (necessitation). -/
  D1 : ∀ {a : Sent}, Prov a → Prov (box a)
  /-- Second derivability condition (internal modus ponens). -/
  D2 : ∀ a b : Sent, Prov (imp (box (imp a b)) (imp (box a) (box b)))
  /-- Third derivability condition (internal necessitation). -/
  D3 : ∀ a : Sent, Prov (imp (box a) (box (box a)))

namespace ProvabilityFramework

variable {F : ProvabilityFramework}

/-- Negation, defined as implication into falsum. -/
