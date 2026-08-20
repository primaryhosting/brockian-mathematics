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

theorem contrapose {p q : T.Sentence} (h : T.Prov (T.imp p q)) :
    T.Prov (T.imp (T.neg q) (T.neg p)) :=
  syl_left h T.bot

/-- Internal necessitation of an implication: from `⊢ p → q` infer `⊢ □p → □q`. -/
