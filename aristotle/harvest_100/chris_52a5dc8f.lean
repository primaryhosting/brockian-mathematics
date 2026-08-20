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
def Consistent : Prop := ∃ p, ¬ T.Thm p

variable {T}

/-- Hypothetical syllogism: from `⊢ p → q` and `⊢ q → r` infer `⊢ p → r`. -/
theorem syl {p q r : T.Sentence} (hpq : T.Thm (T.imp p q)) (hqr : T.Thm (T.imp q r)) :
    T.Thm (T.imp p r) :=
  T.mp (T.mp (T.ax_s p q r) (T.mp (T.ax_k (T.imp q r) p) hqr)) hpq

/-- Contraction: from `⊢ p → (q → r)` and `⊢ p → q` infer `⊢ p → r`. -/
theorem contract {p q r : T.Sentence} (h₁ : T.Thm (T.imp p (T.imp q r)))
    (h₂ : T.Thm (T.imp p q)) : T.Thm (T.imp p r) :=
  T.mp (T.mp (T.ax_s p q r) h₁) h₂

/-- **Löb's theorem.**  If a theory satisfying the derivability conditions proves
the reflection instance `□p → p`, then it already proves `p`. -/
theorem loeb {p : T.Sentence} (h : T.Thm (T.imp (T.box p) p)) : T.Thm p := by
  obtain ⟨d, hd₁, hd₂⟩ := T.diag p
  -- `⊢ □d → □(□d → p)`
  have step₁ : T.Thm (T.imp (T.box d) (T.box (T.imp (T.box d) p))) :=
    T.mp (T.distr d (T.imp (T.box d) p)) (T.nec hd₁)
  -- `⊢ □d → (□□d → □p)`
  have step₂ : T.Thm (T.imp (T.box d) (T.imp (T.box (T.box d)) (T.box p))) :=
    syl step₁ (T.distr (T.box d) p)
  -- `⊢ □d → □p`
  have step₃ : T.Thm (T.imp (T.box d) (T.box p)) := contract step₂ (T.four d)
  -- `⊢ □d → p`
  have step₄ : T.Thm (T.imp (T.box d) p) := syl step₃ h
  -- hence `⊢ d`, so `⊢ □d`, so `⊢ p`
  have hdthm : T.Thm d := T.mp hd₂ step₄
  exact T.mp step₄ (T.nec hdthm)

end ProvabilityTheory

/-- **No self trust (Löb).**  A consistent theory cannot prove the reflection
principle `Prov(⌜p⌝) → p` for any sentence `p` it does not prove.

Formally: if `T` satisfies the Hilbert–Bernays–Löb derivability conditions and the
diagonal lemma, `T` is consistent, and `p` is not provable in `T`, then `T` does
not prove `□p → p`.

(The consistency hypothesis `hcon` was requested in the statement; the proof does
not in fact need it, since the existence of the unprovable sentence `p` already
witnesses consistency.) -/
theorem loeb_no_self_trust (T : ProvabilityTheory) (_hcon : T.Consistent)
    {p : T.Sentence} (hp : ¬ T.Thm p) : ¬ T.Thm (T.imp (T.box p) p) :=
  fun h => hp (ProvabilityTheory.loeb h)

/-- Contrapositive form: a theory proving its full reflection schema
`□p → p` for every sentence `p` proves everything, hence is inconsistent. -/
theorem inconsistent_of_reflection (T : ProvabilityTheory)
    (h : ∀ p, T.Thm (T.imp (T.box p) p)) : ¬ T.Consistent := by
  rintro ⟨p, hp⟩
  exact hp (ProvabilityTheory.loeb (h p))

/-! ### Non-vacuity

The hypotheses above are satisfiable by a consistent theory, so the target
statement is not vacuous.  Here is a two-element model (`Bool`, with `box`
constantly `true` and `Thm p ↔ p = true`); it is consistent, since `false` is
not a theorem. -/

/-- A consistent instance of `ProvabilityTheory`, witnessing that the hypotheses
of `loeb_no_self_trust` are satisfiable. -/
def boolTheory : ProvabilityTheory where
  Sentence := Bool
  imp a b := !a || b
  box _ := true
  Thm a := a = true
  mp := by rintro p q h₁ h₂; revert h₁ h₂; revert p q; decide
  ax_k := by decide
  ax_s := by decide
  nec := by rintro p h; revert h; revert p; decide
  distr := by decide
  four := by decide
  diag p := ⟨p, by revert p; decide, by revert p; decide⟩

theorem boolTheory_consistent : boolTheory.Consistent :=
  ⟨false, by simp [boolTheory]⟩

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

