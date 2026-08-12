/-!
# Goedel Second Incompleteness
Category: Frontier — Set Theory
Target: Frontier.Goedel_second_incompleteness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file formalizes Gödel's second incompleteness theorem in its standard abstract
(Hilbert–Bernays–Löb) form:

  no consistent theory whose provability predicate satisfies the three derivability
  conditions and which admits a Gödel (diagonal) sentence can prove its own consistency.

A consistent recursively axiomatized theory `T` extending `PA` is exactly a situation in
which these hypotheses are met: recursive axiomatizability gives a `Σ₁` provability
predicate `Prov_T`, extension of `PA` gives the three Hilbert–Bernays–Löb derivability
conditions `D1`, `D2`, `D3` for it, and the diagonal lemma supplies a sentence `g` with
`T ⊢ g ↔ ¬ Prov_T(⌜g⌝)`.  The conclusion `¬ T ⊢ Con_T` is then the content of
`Frontier.Goedel_second_incompleteness` below.

The underlying logic is presented as the implicational Hilbert calculus (axioms `K`, `S`
and modus ponens), with `⊥` an arbitrary sentence; negation is `¬a := a → ⊥`, and the
consistency statement is `Con := □⊥ → ⊥`.
-/

namespace Frontier

/-- An abstract provability system: a set of sentences with implication, falsum, an
internal provability operator `box`, and an external provability predicate satisfying the
implicational Hilbert axioms together with the Hilbert–Bernays–Löb derivability
conditions. -/
structure ProvabilitySystem where
  /-- The type of sentences of the theory. -/
  Sentence : Type
  /-- Implication between sentences. -/
  imp : Sentence → Sentence → Sentence
  /-- The false sentence. -/
  bot : Sentence
  /-- The internal provability operator: `box a` expresses "`a` is provable". -/
  box : Sentence → Sentence
  /-- The (external) predicate "the theory proves this sentence". -/
  Provable : Sentence → Prop
  /-- Hilbert axiom `K`. -/
  ax_K : ∀ a b, Provable (imp a (imp b a))
  /-- Hilbert axiom `S`. -/
  ax_S : ∀ a b c, Provable (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  /-- Modus ponens. -/
  modus_ponens : ∀ {a b}, Provable (imp a b) → Provable a → Provable b
  /-- First derivability condition: provability is internally witnessed. -/
  D1 : ∀ {a}, Provable a → Provable (box a)
  /-- Second derivability condition: internal provability is closed under modus ponens. -/
  D2 : ∀ a b, Provable (imp (box (imp a b)) (imp (box a) (box b)))
  /-- Third derivability condition: internal provability is internally provable. -/
  D3 : ∀ a, Provable (imp (box a) (box (box a)))

namespace ProvabilitySystem

variable (T : ProvabilitySystem)

/-- Negation, defined as implication of falsum. -/
def neg (a : T.Sentence) : T.Sentence := T.imp a T.bot

/-- The theory is consistent when it does not prove `⊥`. -/
def Consistent : Prop := ¬ T.Provable T.bot

/-- The internal consistency statement `Con := □⊥ → ⊥`. -/
def ConSentence : T.Sentence := T.imp (T.box T.bot) T.bot

/-- `g` is a Gödel sentence for `T`: the theory proves `g ↔ ¬□g`. -/
def IsGoedelSentence (g : T.Sentence) : Prop :=
  T.Provable (T.imp g (T.neg (T.box g))) ∧ T.Provable (T.imp (T.neg (T.box g)) g)

variable {T}

/-- Hypothetical syllogism inside the object logic. -/
theorem imp_trans {a b c : T.Sentence} (hab : T.Provable (T.imp a b))
    (hbc : T.Provable (T.imp b c)) : T.Provable (T.imp a c) :=
  T.modus_ponens (T.modus_ponens (T.ax_S a b c)
    (T.modus_ponens (T.ax_K (T.imp b c) a) hbc)) hab

/-- The `S`-combinator step: from `a → b` and `a → (b → c)` infer `a → c`. -/
theorem imp_dist {a b c : T.Sentence} (h1 : T.Provable (T.imp a (T.imp b c)))
    (h2 : T.Provable (T.imp a b)) : T.Provable (T.imp a c) :=
  T.modus_ponens (T.modus_ponens (T.ax_S a b c) h1) h2

/-- Necessitation of an implication: from `⊢ a → b` infer `⊢ □a → □b`. -/
theorem box_imp {a b : T.Sentence} (h : T.Provable (T.imp a b)) :
    T.Provable (T.imp (T.box a) (T.box b)) :=
  T.modus_ponens (T.D2 a b) (T.D1 h)

/-- Key lemma: from a Gödel sentence one derives `⊢ □g → □⊥`. -/
theorem box_goedel_imp_box_bot {g : T.Sentence} (hg : T.IsGoedelSentence g) :
    T.Provable (T.imp (T.box g) (T.box T.bot)) :=
  imp_dist (imp_trans (box_imp hg.1) (T.D2 (T.box g) T.bot)) (T.D3 g)

/-- If `T` is consistent, then a Gödel sentence for `T` is not provable in `T`
(Gödel's *first* incompleteness theorem, the unprovability half). -/
theorem goedel_sentence_not_provable {g : T.Sentence} (hg : T.IsGoedelSentence g)
    (hcon : T.Consistent) : ¬ T.Provable g := by
  intro hgp
  exact hcon (T.modus_ponens (T.modus_ponens hg.1 hgp) (T.D1 hgp))

/-- If `T` proves its own consistency, then it proves its Gödel sentence. -/
theorem provable_goedel_of_provable_con {g : T.Sentence} (hg : T.IsGoedelSentence g)
    (hConT : T.Provable T.ConSentence) : T.Provable g :=
  T.modus_ponens hg.2 (imp_trans (box_goedel_imp_box_bot hg) hConT)

end ProvabilitySystem

/-- **Gödel's second incompleteness theorem** (abstract Hilbert–Bernays–Löb form).

No consistent theory satisfying the derivability conditions and possessing a Gödel
sentence proves its own consistency statement `Con := □⊥ → ⊥`.

Since a consistent recursively axiomatized theory extending `PA` satisfies exactly these
hypotheses (its `Σ₁` provability predicate obeys `D1`–`D3`, and the diagonal lemma
provides the Gödel sentence `g` with `T ⊢ g ↔ ¬□g`), such a theory cannot prove its own
consistency. -/
theorem Goedel_second_incompleteness (T : ProvabilitySystem) (g : T.Sentence)
    (hg : T.IsGoedelSentence g) (hcon : T.Consistent) : ¬ T.Provable T.ConSentence :=
  fun hConT =>
    ProvabilitySystem.goedel_sentence_not_provable hg hcon
      (ProvabilitySystem.provable_goedel_of_provable_con hg hConT)

/-- Sanity check (non-vacuity): the axioms of `ProvabilitySystem` together with
consistency are jointly satisfiable.  Here sentences are Lean propositions, implication
is implication, `⊥` is `False`, and the provability operators are the identity/truth. -/
def truthSystem : ProvabilitySystem where
  Sentence := Prop
  imp a b := a → b
  bot := False
  box a := a
  Provable a := a
  ax_K _ _ := fun ha _ => ha
  ax_S _ _ _ := fun f g a => f a (g a)
  modus_ponens := fun f a => f a
  D1 := fun h => h
  D2 _ _ := fun f a => f a
  D3 _ := fun h => h

theorem truthSystem_consistent : truthSystem.Consistent := id

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

