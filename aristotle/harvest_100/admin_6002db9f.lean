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
theorem models_axK (T : L.Theory) (a b : L.Sentence) : T ⊨ᵇ (a ⟹ (b ⟹ a)) := by
  rw [Theory.models_sentence_iff]
  intro M
  simp only [Sentence.Realize, Formula.Realize, BoundedFormula.realize_imp]
  tauto

/-- Entailment of first-order sentences contains the axiom scheme
`(a → (b → c)) → ((a → b) → (a → c))`. -/
theorem models_axS (T : L.Theory) (a b c : L.Sentence) :
    T ⊨ᵇ ((a ⟹ (b ⟹ c)) ⟹ ((a ⟹ b) ⟹ (a ⟹ c))) := by
  rw [Theory.models_sentence_iff]
  intro M
  simp only [Sentence.Realize, Formula.Realize, BoundedFormula.realize_imp]
  tauto

/-- The `ProvabilityFramework` of `L`-sentences over a theory `T`, where `Pr` is an
internal provability predicate satisfying the derivability conditions. -/
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
def neg (F : ProvabilityFramework) (a : F.Sent) : F.Sent := F.imp a F.bot

/-- The consistency statement `Con_T`, i.e. `¬ □⊥`. -/
def Con (F : ProvabilityFramework) : F.Sent := F.neg (F.box F.bot)

/-- The theory is consistent when it does not prove falsum. -/
def Consistent (F : ProvabilityFramework) : Prop := ¬ F.Prov F.bot

/-- A *Gödel sentence* is a sentence provably equivalent to its own unprovability.
Its existence is guaranteed by the diagonal lemma for any recursively
axiomatized theory extending `PA`. -/
def IsGoedelSentence (F : ProvabilityFramework) (g : F.Sent) : Prop :=
  F.Prov (F.imp g (F.neg (F.box g))) ∧ F.Prov (F.imp (F.neg (F.box g)) g)

/-- Weakening: a provable sentence is provable under any hypothesis. -/
theorem prov_imp_of_prov {a b : F.Sent} (h : F.Prov b) : F.Prov (F.imp a b) :=
  F.mp (F.axK b a) h

/-- The `S`-rule: from `a → (b → c)` and `a → b` infer `a → c`. -/
theorem imp_trans_S {a b c : F.Sent} (h₁ : F.Prov (F.imp a (F.imp b c)))
    (h₂ : F.Prov (F.imp a b)) : F.Prov (F.imp a c) :=
  F.mp (F.mp (F.axS a b c) h₁) h₂

/-- Hypothetical syllogism. -/
theorem imp_trans {a b c : F.Sent} (h₁ : F.Prov (F.imp a b))
    (h₂ : F.Prov (F.imp b c)) : F.Prov (F.imp a c) :=
  imp_trans_S (prov_imp_of_prov h₂) h₁

/-- Provable implications are internally provable: `⊢ a → b` gives `⊢ □a → □b`. -/
theorem box_mono {a b : F.Sent} (h : F.Prov (F.imp a b)) :
    F.Prov (F.imp (F.box a) (F.box b)) :=
  F.mp (F.D2 a b) (F.D1 h)

/-- Half of Gödel's first incompleteness theorem, formalized inside the theory:
if `g` is a Gödel sentence then `T ⊢ □g → □⊥`. -/
theorem box_goedel_imp_box_bot {g : F.Sent} (hg : F.IsGoedelSentence g) :
    F.Prov (F.imp (F.box g) (F.box F.bot)) :=
  imp_trans_S
    (imp_trans (box_mono hg.1) (F.D2 (F.box g) F.bot))
    (F.D3 g)

/--
**Gödel's second incompleteness theorem.**

No consistent, recursively axiomatized theory extending `PA` proves its own
consistency: if `F` satisfies the derivability conditions, has a Gödel sentence
(supplied by the diagonal lemma) and is consistent, then `F` does not prove
`Con_F = ¬ □⊥`.
-/
theorem Goedel_second_incompleteness (F : ProvabilityFramework)
    (hdiag : ∃ g : F.Sent, F.IsGoedelSentence g) (hcon : F.Consistent) :
    ¬ F.Prov F.Con := by
  obtain ⟨g, hg₁, hg₂⟩ := hdiag
  intro hC
  -- From `T ⊢ Con` we get `T ⊢ ¬ □g`, hence `T ⊢ g`.
  have hng : F.Prov (F.neg (F.box g)) :=
    imp_trans (box_goedel_imp_box_bot ⟨hg₁, hg₂⟩) hC
  have hgprov : F.Prov g := F.mp hg₂ hng
  -- But then `T ⊢ □g`, and `g` says `¬ □g`, so `T ⊢ ⊥`.
  exact hcon (F.mp (F.mp hg₁ hgprov) (F.D1 hgprov))

end ProvabilityFramework

/-- **Gödel's second incompleteness theorem** (top-level statement).

For every framework `F` of sentences with an arithmetized provability predicate
satisfying the Hilbert–Bernays–Löb derivability conditions and admitting a Gödel
sentence — in particular for every recursively axiomatized theory extending
`PA` — consistency of `F` implies that `F` does not prove its own consistency
statement `Con_F`. -/
theorem Goedel_second_incompleteness (F : ProvabilityFramework)
    (hdiag : ∃ g : F.Sent, F.IsGoedelSentence g) (hcon : F.Consistent) :
    ¬ F.Prov F.Con :=
  ProvabilityFramework.Goedel_second_incompleteness F hdiag hcon

/-! ### Non-vacuity

The hypotheses of the theorem are simultaneously satisfiable: below is a
consistent framework satisfying all the derivability conditions and possessing a
Gödel sentence, so the theorem above is not vacuously true. -/

/-- A concrete two-element framework satisfying every hypothesis. -/
def boolFramework : ProvabilityFramework where
  Sent := Bool
  imp a b := !a || b
  bot := false
  box _ := true
  Prov a := a = true
  mp {a b} := by revert a b; decide
  axK := by decide
  axS := by decide
  D1 {a} := by revert a; decide
  D2 := by decide
  D3 := by decide

theorem boolFramework_consistent : boolFramework.Consistent :=
  fun h => Bool.noConfusion h

theorem boolFramework_hasGoedelSentence :
    ∃ g : boolFramework.Sent, boolFramework.IsGoedelSentence g :=
  ⟨false, rfl, rfl⟩

/-- The theorem applies non-vacuously to `boolFramework`. -/
theorem boolFramework_not_prov_Con : ¬ boolFramework.Prov boolFramework.Con :=
  Goedel_second_incompleteness boolFramework boolFramework_hasGoedelSentence
    boolFramework_consistent

end Frontier

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

