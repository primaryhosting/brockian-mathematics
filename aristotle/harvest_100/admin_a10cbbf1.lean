import Mathlib

/-!
# Löb's theorem: a theory cannot trust itself

This file develops, from scratch, an abstract axiomatisation of a formal theory equipped with
a provability predicate satisfying the Hilbert–Bernays–Löb derivability conditions and admitting
Gödel fixed points (the diagonal lemma).  In this setting we prove Löb's theorem and deduce the
target result:

* `Frontier.loeb_no_self_trust` : a consistent theory cannot prove the *reflection principle*
  `□φ → φ` for a sentence `φ` that it does not prove.

As a special case we obtain the abstract form of Gödel's second incompleteness theorem
(`Frontier.ProvabilitySystem.godel_second`): a consistent theory does not prove
`□⊥ → ⊥`, i.e. it does not prove its own consistency.

Everything is stated for an arbitrary `Frontier.ProvabilitySystem`; the structure is shown to be
satisfiable together with the consistency hypothesis by `Frontier.boolSystem`.
-/

namespace Frontier

/--
An abstract *provability system*: a set of sentences closed under implication, with a
distinguished falsum, a provability (box) operator on sentences and a provability predicate,
subject to

* a Hilbert-style axiomatisation of implicational logic (`axK`, `axS`, `mp`),
* ex falso (`explosion`),
* the three Hilbert–Bernays–Löb derivability conditions
  (`necessitation`, `boxImp`, `boxBox`),
* the diagonal (fixed point) lemma (`diagonal`).

These are exactly the properties that an arithmetised provability predicate for a recursively
axiomatised, sufficiently strong theory (such as `PA`) enjoys.
-/
structure ProvabilitySystem where
  /-- The type of sentences of the theory. -/
  Sentence : Type
  /-- Implication between sentences. -/
  imp : Sentence → Sentence → Sentence
  /-- The false sentence. -/
  bot : Sentence
  /-- The provability operator: `box p` is the sentence "`p` is provable". -/
  box : Sentence → Sentence
  /-- `Prov p` means that the theory proves the sentence `p`. -/
  Prov : Sentence → Prop
  /-- Hilbert axiom scheme K. -/
  axK : ∀ p q, Prov (imp p (imp q p))
  /-- Hilbert axiom scheme S. -/
  axS : ∀ p q r, Prov (imp (imp p (imp q r)) (imp (imp p q) (imp p r)))
  /-- Modus ponens. -/
  mp : ∀ {p q}, Prov (imp p q) → Prov p → Prov q
  /-- Ex falso quodlibet. -/
  explosion : ∀ p, Prov (imp bot p)
  /-- First derivability condition. -/
  necessitation : ∀ {p}, Prov p → Prov (box p)
  /-- Second derivability condition (the modal axiom K). -/
  boxImp : ∀ p q, Prov (imp (box (imp p q)) (imp (box p) (box q)))
  /-- Third derivability condition. -/
  boxBox : ∀ p, Prov (imp (box p) (box (box p)))
  /-- The diagonal lemma: every `p` has a Gödel fixed point `q` provably equivalent to
  `box q → p`. -/
  diagonal : ∀ p, ∃ q, Prov (imp q (imp (box q) p)) ∧ Prov (imp (imp (box q) p) q)

namespace ProvabilitySystem

variable (S : ProvabilitySystem)

/-- The theory is consistent if it does not prove falsum. -/
def Consistent : Prop := ¬ S.Prov S.bot

/-- The reflection principle for `φ`: the sentence "if `φ` is provable then `φ`". -/
def Reflection (φ : S.Sentence) : S.Sentence := S.imp (S.box φ) φ

variable {S}

/-- `p → p` is provable. -/
theorem imp_refl (p : S.Sentence) : S.Prov (S.imp p p) :=
  S.mp (S.mp (S.axS p (S.imp p p) p) (S.axK p (S.imp p p))) (S.axK p p)

/-- A provable sentence is implied by anything. -/
theorem imp_intro {q : S.Sentence} (hq : S.Prov q) (p : S.Sentence) : S.Prov (S.imp p q) :=
  S.mp (S.axK q p) hq

/-- Distribution of a hypothesis over an implication. -/
theorem imp_mp {p q r : S.Sentence} (h₁ : S.Prov (S.imp p (S.imp q r)))
    (h₂ : S.Prov (S.imp p q)) : S.Prov (S.imp p r) :=
  S.mp (S.mp (S.axS p q r) h₁) h₂

/-- Transitivity of provable implication. -/
theorem imp_trans {p q r : S.Sentence} (h₁ : S.Prov (S.imp p q)) (h₂ : S.Prov (S.imp q r)) :
    S.Prov (S.imp p r) :=
  imp_mp (imp_intro h₂ p) h₁

/-- The box operator is monotone on provable implications. -/
theorem box_mono {p q : S.Sentence} (h : S.Prov (S.imp p q)) :
    S.Prov (S.imp (S.box p) (S.box q)) :=
  S.mp (S.boxImp p q) (S.necessitation h)

/-- **Löb's theorem**: if the theory proves the reflection principle for `φ`, then it proves `φ`.
-/
theorem loeb {φ : S.Sentence} (h : S.Prov (S.Reflection φ)) : S.Prov φ := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := S.diagonal φ
  -- `□ψ → □(□ψ → φ)`
  have step1 : S.Prov (S.imp (S.box ψ) (S.box (S.imp (S.box ψ) φ))) := box_mono hψ₁
  -- `□ψ → (□□ψ → □φ)`
  have step2 : S.Prov (S.imp (S.box ψ) (S.imp (S.box (S.box ψ)) (S.box φ))) :=
    imp_trans step1 (S.boxImp (S.box ψ) φ)
  -- `□ψ → □φ`, using the third derivability condition
  have step3 : S.Prov (S.imp (S.box ψ) (S.box φ)) := imp_mp step2 (S.boxBox ψ)
  -- `□ψ → φ`, using the assumed reflection principle
  have step4 : S.Prov (S.imp (S.box ψ) φ) := imp_trans step3 h
  -- hence `ψ` itself is provable, hence so is `□ψ`
  have step5 : S.Prov ψ := S.mp hψ₂ step4
  exact S.mp step4 (S.necessitation step5)

/-- Contrapositive of Löb's theorem: an unprovable sentence has an unprovable reflection
principle. -/
theorem not_prov_reflection {φ : S.Sentence} (hφ : ¬ S.Prov φ) : ¬ S.Prov (S.Reflection φ) :=
  fun h => hφ (loeb h)

/-- **Gödel's second incompleteness theorem**, abstract form: a consistent theory does not prove
the reflection principle for falsum, i.e. it does not prove its own consistency statement
`□⊥ → ⊥`. -/
theorem godel_second (hcon : S.Consistent) : ¬ S.Prov (S.Reflection S.bot) :=
  not_prov_reflection hcon

end ProvabilitySystem

/--
**A consistent theory cannot trust itself.**

If `S` is a consistent provability system (satisfying the derivability conditions and the
diagonal lemma) and `φ` is a sentence that `S` does not prove, then `S` does not prove the
reflection principle `□φ → φ` for `φ`.

The hypothesis `hcon` that `S` is consistent is included because it is part of the statement as
posed; Löb's theorem in fact yields the conclusion from the unprovability of `φ` alone (and, of
course, consistency is what guarantees that unprovable sentences exist at all — see
`Frontier.ProvabilitySystem.godel_second`, where `φ = ⊥`).
-/
theorem loeb_no_self_trust (S : ProvabilitySystem) (hcon : S.Consistent) {φ : S.Sentence}
    (hφ : ¬ S.Prov φ) : ¬ S.Prov (S.imp (S.box φ) φ) :=
  ProvabilitySystem.not_prov_reflection hφ

/-! ### Non-vacuity

The axioms of `ProvabilitySystem` together with consistency are satisfiable, so the theorem above
is not vacuous. -/

/-- A (very simple) consistent provability system: sentences are booleans, `Prov p` says that `p`
is `true`, and `box` is constantly `true`. -/
def boolSystem : ProvabilitySystem where
  Sentence := Bool
  imp p q := (!p || q)
  bot := false
  box _ := true
  Prov p := p = true
  axK p q := by revert p q; decide
  axS p q r := by revert p q r; decide
  mp {p q} := by revert p q; decide
  explosion p := by revert p; decide
  necessitation := by intro p _; rfl
  boxImp p q := by revert p q; decide
  boxBox p := by revert p; decide
  diagonal p := ⟨p, by revert p; decide, by revert p; decide⟩

theorem boolSystem_consistent : boolSystem.Consistent := by
  intro h
  exact Bool.false_ne_true h

/-- An instance of the main theorem: `boolSystem` is consistent and does not prove the
reflection principle for its (unprovable) falsum. -/
example : ¬ boolSystem.Prov (boolSystem.imp (boolSystem.box boolSystem.bot) boolSystem.bot) :=
  loeb_no_self_trust boolSystem boolSystem_consistent boolSystem_consistent

end Frontier

#print axioms Frontier.loeb_no_self_trust
#print axioms Frontier.ProvabilitySystem.loeb
#print axioms Frontier.ProvabilitySystem.godel_second

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

