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

