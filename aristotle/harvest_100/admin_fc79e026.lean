/-!
# Goedel Second Incompleteness
Category: Frontier — Set Theory
Target: Frontier.Goedel_second_incompleteness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Mathlib does not contain any arithmetization of syntax, so the statement

  "no consistent recursively axiomatized theory extending `PA` proves its own consistency"

is formalized here in the standard *abstract* (Hilbert–Bernays–Löb) way, which is exactly the
Lean-checked reduction requested:

* A `ProvabilitySystem` packages a set of sentences with implication `imp`, falsum `bot`, a
  provability predicate `Prov` (the theorems of the theory) and a *provability operator* `box`
  (the arithmetized provability predicate `Prov_T(⌜·⌝)` of the theory).
* The hypotheses are precisely: closure of `Prov` under modus ponens together with the
  implicational Hilbert axioms `K` and `S` (available in any theory extending `PA`), and the
  three Hilbert–Bernays–Löb derivability conditions

    D1: `⊢ p  →  ⊢ □p`,
    D2: `⊢ □(p → q) → (□p → □q)`,
    D3: `⊢ □p → □□p`.

  These hold for the standard provability predicate of any consistent recursively axiomatized
  theory extending `PA` (this arithmetical fact is the part not formalized here).
* The remaining input is the diagonal lemma: existence of a Gödel sentence `g` with
  `⊢ g ↔ ¬□g`.

Under exactly these hypotheses we prove, fully formally:

* `Frontier.Goedel_first_incompleteness` : a consistent such theory does not prove `g`;
* `Frontier.Goedel_second_incompleteness` : a consistent such theory does not prove its own
  consistency statement `Con := ¬□⊥`.

The framework is shown to be non-vacuous by `Frontier.toyExample`, an explicitly constructed
provability system satisfying all the hypotheses, including consistency and the diagonal lemma.
-/

namespace Frontier

/-- An abstract provability system: the syntactic skeleton (`imp`, `bot`, `box`) of a theory
together with its set `Prov` of theorems, satisfying implicational logic and the
Hilbert–Bernays–Löb derivability conditions. -/
structure ProvabilitySystem where
  /-- The type of sentences of the theory. -/
  Sentence : Type
  /-- Falsum. -/
  bot : Sentence
  /-- Implication. -/
  imp : Sentence → Sentence → Sentence
  /-- The provability operator: `box p` is the arithmetized statement "`p` is provable". -/
  box : Sentence → Sentence
  /-- `Prov p` says that `p` is a theorem of the theory. -/
  Prov : Sentence → Prop
  /-- Hilbert axiom `K`. -/
  ax_K : ∀ p q, Prov (imp p (imp q p))
  /-- Hilbert axiom `S`. -/
  ax_S : ∀ p q r, Prov (imp (imp p (imp q r)) (imp (imp p q) (imp p r)))
  /-- Closure under modus ponens. -/
  mp : ∀ {p q}, Prov (imp p q) → Prov p → Prov q
  /-- First derivability condition (necessitation). -/
  HBL1 : ∀ {p}, Prov p → Prov (box p)
  /-- Second derivability condition (distribution). -/
  HBL2 : ∀ p q, Prov (imp (box (imp p q)) (imp (box p) (box q)))
  /-- Third derivability condition. -/
  HBL3 : ∀ p, Prov (imp (box p) (box (box p)))

namespace ProvabilitySystem

variable (T : ProvabilitySystem)

/-- Negation, defined as implication to falsum. -/
def neg (p : T.Sentence) : T.Sentence := T.imp p T.bot

/-- The consistency statement `Con_T := ¬ □⊥`. -/
def Con : T.Sentence := T.neg (T.box T.bot)

/-- The theory is consistent: it does not prove falsum. -/
def Consistent : Prop := ¬ T.Prov T.bot

/-- `g` is a Gödel sentence: the theory proves `g ↔ ¬□g`. -/
def IsGoedelSentence (g : T.Sentence) : Prop :=
  T.Prov (T.imp g (T.neg (T.box g))) ∧ T.Prov (T.imp (T.neg (T.box g)) g)

variable {T}

/-- `⊢ p → p`. -/
theorem imp_self (p : T.Sentence) : T.Prov (T.imp p p) :=
  T.mp (T.mp (T.ax_S p (T.imp p p) p) (T.ax_K p (T.imp p p))) (T.ax_K p p)

/-- Weakening: from `⊢ q` infer `⊢ p → q`. -/
theorem imp_intro {q : T.Sentence} (p : T.Sentence) (h : T.Prov q) : T.Prov (T.imp p q) :=
  T.mp (T.ax_K q p) h

/-- Distribution of a proved implication under a common antecedent. -/
theorem imp_distrib {p q r : T.Sentence} (h : T.Prov (T.imp q r)) :
    T.Prov (T.imp (T.imp p q) (T.imp p r)) :=
  T.mp (T.ax_S p q r) (imp_intro p h)

/-- Syllogism / composition: from `⊢ p → q` and `⊢ q → r` infer `⊢ p → r`. -/
theorem syl {p q r : T.Sentence} (h₁ : T.Prov (T.imp p q)) (h₂ : T.Prov (T.imp q r)) :
    T.Prov (T.imp p r) :=
  T.mp (imp_distrib h₂) h₁

/-- Composition in the antecedent: from `⊢ p → q` infer `⊢ (q → r) → (p → r)`. -/
theorem syl_left {p q : T.Sentence} (h : T.Prov (T.imp p q)) (r : T.Sentence) :
    T.Prov (T.imp (T.imp q r) (T.imp p r)) :=
  T.mp
    (T.mp (T.ax_S (T.imp q r) (T.imp p q) (T.imp p r))
      (syl (T.ax_K (T.imp q r) p) (T.ax_S p q r)))
    (imp_intro (T.imp q r) h)

/-- Contraposition (implicational form): from `⊢ p → q` infer `⊢ ¬q → ¬p`. -/
theorem contrapose {p q : T.Sentence} (h : T.Prov (T.imp p q)) :
    T.Prov (T.imp (T.neg q) (T.neg p)) :=
  syl_left h T.bot

/-- Internal necessitation of an implication: from `⊢ p → q` infer `⊢ □p → □q`. -/
theorem box_mono {p q : T.Sentence} (h : T.Prov (T.imp p q)) :
    T.Prov (T.imp (T.box p) (T.box q)) :=
  T.mp (T.HBL2 p q) (T.HBL1 h)

/-- **Formalized first incompleteness theorem**: for a Gödel sentence `g`, the theory proves
`□g → □⊥`, hence (contraposing) `Con → ¬□g`. This is the heart of the argument, and the only
place where the third derivability condition is used. -/
theorem box_goedel_imp_box_bot {g : T.Sentence} (hg : T.IsGoedelSentence g) :
    T.Prov (T.imp (T.box g) (T.box T.bot)) := by
  -- `⊢ □g → □(□g → ⊥)` from `⊢ g → (□g → ⊥)`
  have h1 : T.Prov (T.imp (T.box g) (T.box (T.neg (T.box g)))) := box_mono hg.1
  -- `⊢ □(□g → ⊥) → (□□g → □⊥)`
  have h2 : T.Prov (T.imp (T.box (T.neg (T.box g))) (T.imp (T.box (T.box g)) (T.box T.bot))) :=
    T.HBL2 (T.box g) T.bot
  -- `⊢ □g → (□□g → □⊥)`
  have h3 : T.Prov (T.imp (T.box g) (T.imp (T.box (T.box g)) (T.box T.bot))) := syl h1 h2
  -- combine with `⊢ □g → □□g` using axiom `S`
  exact T.mp (T.mp (T.ax_S (T.box g) (T.box (T.box g)) (T.box T.bot)) h3) (T.HBL3 g)

/-- The theory proves `Con → g` for any Gödel sentence `g`. -/
theorem con_imp_goedel {g : T.Sentence} (hg : T.IsGoedelSentence g) :
    T.Prov (T.imp T.Con g) :=
  syl (contrapose (box_goedel_imp_box_bot hg)) hg.2

/-- **Gödel's first incompleteness theorem** (abstract form): a consistent theory satisfying the
derivability conditions does not prove its Gödel sentence. -/
theorem goedel_first {g : T.Sentence} (hg : T.IsGoedelSentence g) (hcon : T.Consistent) :
    ¬ T.Prov g := by
  intro hpg
  exact hcon (T.mp (T.mp hg.1 hpg) (T.HBL1 hpg))

/-- **Gödel's second incompleteness theorem** (abstract form). -/
theorem goedel_second (hdiag : ∃ g, T.IsGoedelSentence g) (hcon : T.Consistent) :
    ¬ T.Prov T.Con := by
  obtain ⟨g, hg⟩ := hdiag
  intro hProvCon
  exact goedel_first hg hcon (T.mp (con_imp_goedel hg) hProvCon)

end ProvabilitySystem

/--
**Gödel's second incompleteness theorem.**

No consistent theory `T` that is strong enough to satisfy the Hilbert–Bernays–Löb derivability
conditions (in particular, no consistent recursively axiomatized theory extending `PA`, for which
these conditions hold of the standard provability predicate) proves its own consistency statement
`Con_T = ¬ Prov_T(⌜⊥⌝)`.
-/
theorem Goedel_second_incompleteness (T : ProvabilitySystem)
    (hdiag : ∃ g, T.IsGoedelSentence g) (hcon : T.Consistent) :
    ¬ T.Prov T.Con :=
  ProvabilitySystem.goedel_second hdiag hcon

/--
**Gödel's first incompleteness theorem** (the "base case" of the same reduction): under the same
hypotheses the Gödel sentence is unprovable.
-/
theorem Goedel_first_incompleteness (T : ProvabilitySystem) {g : T.Sentence}
    (hg : T.IsGoedelSentence g) (hcon : T.Consistent) :
    ¬ T.Prov g :=
  ProvabilitySystem.goedel_first hg hcon

/-! ## Non-vacuity

We exhibit an explicit provability system satisfying *all* hypotheses of the theorems above,
including consistency and the existence of a Gödel sentence, so that the results are not vacuous.
-/

/-- Syntax of the toy example: implicational formulas with falsum and a box. -/
inductive ToyForm : Type
  | bot : ToyForm
  | imp : ToyForm → ToyForm → ToyForm
  | box : ToyForm → ToyForm
  deriving DecidableEq

namespace ToyForm

/-- Boolean evaluation interpreting `box p` as `true`. -/
def eval : ToyForm → Bool
  | bot => false
  | imp p q => !(eval p) || eval q
  | box _ => true

end ToyForm

/-- A consistent provability system satisfying all derivability conditions and possessing a
Gödel sentence (namely `⊥` itself, since `□⊥` is "provable" in this system). -/
def toyExample : ProvabilitySystem where
  Sentence := ToyForm
  bot := ToyForm.bot
  imp := ToyForm.imp
  box := ToyForm.box
  Prov p := p.eval = true
  ax_K p q := by
    simp only [ToyForm.eval]
    cases h : p.eval <;> cases h' : q.eval <;> simp
  ax_S p q r := by
    simp only [ToyForm.eval]
    cases h : p.eval <;> cases h' : q.eval <;> cases h'' : r.eval <;> simp
  mp {p q} h₁ h₂ := by
    simp only [ToyForm.eval, h₂] at h₁
    simpa using h₁
  HBL1 _ := rfl
  HBL2 p q := by simp [ToyForm.eval]
  HBL3 p := by simp [ToyForm.eval]

theorem toyExample_consistent : toyExample.Consistent := by
  simp [ProvabilitySystem.Consistent, toyExample, ToyForm.eval]

theorem toyExample_goedelSentence :
    toyExample.IsGoedelSentence ToyForm.bot := by
  constructor <;> simp [ProvabilitySystem.neg, toyExample, ToyForm.eval]

/-- The theorem applies non-vacuously: the toy system is consistent, has a Gödel sentence, and
therefore does not prove its own consistency. -/
theorem toyExample_not_prov_con : ¬ toyExample.Prov toyExample.Con :=
  Goedel_second_incompleteness toyExample ⟨_, toyExample_goedelSentence⟩ toyExample_consistent

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

