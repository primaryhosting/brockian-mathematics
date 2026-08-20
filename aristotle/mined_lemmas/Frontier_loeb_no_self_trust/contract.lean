/-!
# Loeb No Self Trust
Category: Frontier Mind
Target: Frontier.loeb_no_self_trust
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A *consistent* theory cannot prove the reflection principle `Prov(⌜p⌝) → p` for a
sentence `p` that it does not prove.  This is an immediate consequence of Löb's
theorem, which we prove here from the Hilbert–Bernays–Löb derivability conditions.

Mathlib (at the version pinned by this project) contains no formalization of
provability predicates, the derivability conditions, the diagonal lemma, or Löb's
theorem: searching for `Löb`, `Provable`, provability logic, or `GL` turns up
nothing usable, and Gödel-style incompleteness is not part of Mathlib either.
So the whole development below (abstract syntax, derivability conditions, Löb's
theorem, and the target statement) is built from first principles.

## Set-up

We work abstractly with a `ProvabilityTheory`: a type of sentences equipped with

* an implication connective `imp`,
* a provability operator `box` (`box p` is the sentence "`p` is provable"),
* a theoremhood predicate `Thm`,

subject to:

* the propositional axiom schemas `K` and `S` together with modus ponens
  (this makes `Thm` closed under implicational propositional logic),
* the three Hilbert–Bernays–Löb derivability conditions
  (necessitation, distribution, and `□p → □□p`),
* the diagonal (fixed point) lemma.

Any sufficiently strong theory — e.g. Peano arithmetic with its standard
provability predicate — is an instance of this structure.
-/

namespace Frontier

/-- An abstract provability setting: sentences with an implication connective, a
provability operator `box`, and a theoremhood predicate `Thm` satisfying the
Hilbert–Bernays–Löb derivability conditions, the implicational fragment of
propositional logic, and the diagonal lemma. -/
structure ProvabilityTheory where
  /-- The type of sentences of the theory. -/
  Sentence : Type
  /-- The implication connective. -/
  imp : Sentence → Sentence → Sentence
  /-- `box p` is the sentence expressing "`p` is provable in the theory". -/
  box : Sentence → Sentence
  /-- `Thm p` says that `p` is provable in the theory. -/
  Thm : Sentence → Prop
  /-- Modus ponens. -/
  mp : ∀ {p q}, Thm (imp p q) → Thm p → Thm q
  /-- The propositional axiom schema `K : p → (q → p)`. -/
  ax_k : ∀ p q, Thm (imp p (imp q p))
  /-- The propositional axiom schema
  `S : (p → (q → r)) → ((p → q) → (p → r))`. -/
  ax_s : ∀ p q r, Thm (imp (imp p (imp q r)) (imp (imp p q) (imp p r)))
  /-- First derivability condition (necessitation): what is provable is
  provably provable. -/
  nec : ∀ {p}, Thm p → Thm (box p)
  /-- Second derivability condition: the provability predicate distributes over
  implication. -/
  distr : ∀ p q, Thm (imp (box (imp p q)) (imp (box p) (box q)))
  /-- Third derivability condition: provability is provably transitive,
  `□p → □□p`. -/
  four : ∀ p, Thm (imp (box p) (box (box p)))
  /-- The diagonal (fixed point) lemma: for every `p` there is a sentence `d`
  provably equivalent to `box d → p`. -/
  diag : ∀ p, ∃ d, Thm (imp d (imp (box d) p)) ∧ Thm (imp (imp (box d) p) d)

namespace ProvabilityTheory

variable (T : ProvabilityTheory)

/-- The theory is consistent when some sentence is not provable in it. -/

theorem contract {p q r : T.Sentence} (h₁ : T.Thm (T.imp p (T.imp q r)))
    (h₂ : T.Thm (T.imp p q)) : T.Thm (T.imp p r) :=
  T.mp (T.mp (T.ax_s p q r) h₁) h₂

/-- **Löb's theorem.**  If a theory satisfying the derivability conditions proves
the reflection instance `□p → p`, then it already proves `p`. -/
