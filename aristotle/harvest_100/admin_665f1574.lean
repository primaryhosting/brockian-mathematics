/-!
# Loeb Theorem
Category: Frontier — Set Theory
Target: Frontier.Loeb_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Löb's theorem: *if `PA ⊢ (□φ → φ)` then `PA ⊢ φ`*, where `□φ` is the arithmetized
provability statement `Prov_PA(⌜φ⌝)`.

A search of Mathlib (`lean_local_search`, `exact?`/`apply?`, LeanSearch) turns up **no**
existing declaration about provability predicates, the Hilbert–Bernays–Löb derivability
conditions, the diagonal (fixed point) lemma, or Löb's theorem.  Mathlib's
`Mathlib.ModelTheory.*` develops first-order syntax, satisfaction and (in
`Mathlib.ModelTheory.Satisfiability`) the completeness theorem, but it contains no
arithmetization of syntax, no Gödel numbering, and hence no internal provability
predicate for `PA`.  So the statement has to be formalized from scratch here.

## What is formalized

Löb's theorem is *not* a theorem about the specific theory `PA`: it is a theorem about any
provability predicate satisfying the three Hilbert–Bernays–Löb derivability conditions
together with the diagonal lemma.  These are exactly the properties of `PA`'s provability
predicate `Prov_PA` that Gödel's arithmetization establishes.  We therefore package them
into a structure `Frontier.ProvabilitySystem`:

* a type of sentences with an implication connective `imp`,
* a provability *judgement* `Prov` (read: `PA ⊢ ·`),
* a provability *formula* `box` (read: `□`, i.e. `Prov_PA(⌜·⌝)`),
* modus ponens and the two implicational Hilbert axiom schemes `K`, `S`
  (i.e. `PA` proves all implicational tautologies and is closed under MP),
* **D1** (necessitation):     `⊢ p  ⟹  ⊢ □p`,
* **D2** (distribution):      `⊢ □(p → q) → (□p → □q)`,
* **D3** (formalized D1):     `⊢ □p → □□p`,
* **diagonal lemma**: for every `p` there is a sentence `d` with `⊢ d ↔ (□d → p)`
  (stated as the two implications, to avoid needing a biconditional connective).

`Frontier.Loeb_theorem` then states: in any such system, `Prov (□φ → φ)` implies `Prov φ`.

The axiom set is consistent and non-degenerate: `Frontier.boolSystem` below is an explicit
model in which `Prov` does **not** hold of every sentence, so the theorem is not vacuous.
-/

universe u

namespace Frontier

/-- An abstract **provability system**: a set of sentences together with a provability
judgement `Prov` (`PA ⊢ ·`) and an internal provability formula `box` (`□`, i.e.
`Prov_PA(⌜·⌝)`), satisfying the Hilbert–Bernays–Löb derivability conditions and the
diagonal lemma.  These are precisely the properties of Peano Arithmetic and its
arithmetized provability predicate that Gödel's arithmetization of syntax establishes. -/
structure ProvabilitySystem where
  /-- The type of sentences of the theory. -/
  Sentence : Type u
  /-- The implication connective. -/
  imp : Sentence → Sentence → Sentence
  /-- The internal provability formula: `box p` is the arithmetized statement
  "`p` is provable". -/
  box : Sentence → Sentence
  /-- The provability judgement: `Prov p` means "the theory proves `p`". -/
  Prov : Sentence → Prop
  /-- Modus ponens. -/
  mp : ∀ {p q : Sentence}, Prov (imp p q) → Prov p → Prov q
  /-- The Hilbert axiom scheme `K : p → (q → p)`. -/
  ax_K : ∀ p q : Sentence, Prov (imp p (imp q p))
  /-- The Hilbert axiom scheme `S : (p → (q → r)) → ((p → q) → (p → r))`. -/
  ax_S : ∀ p q r : Sentence,
    Prov (imp (imp p (imp q r)) (imp (imp p q) (imp p r)))
  /-- Derivability condition **D1** (necessitation): if `p` is provable, then the theory
  proves that `p` is provable. -/
  D1 : ∀ {p : Sentence}, Prov p → Prov (box p)
  /-- Derivability condition **D2**: the theory proves that provability distributes over
  implication. -/
  D2 : ∀ p q : Sentence, Prov (imp (box (imp p q)) (imp (box p) (box q)))
  /-- Derivability condition **D3**: the theory proves that provability is provably
  provable. -/
  D3 : ∀ p : Sentence, Prov (imp (box p) (box (box p)))
  /-- The **diagonal lemma** (Gödel's fixed point lemma), in the form needed for Löb's
  theorem: for every sentence `p` there is a sentence `d` provably equivalent to
  `□d → p`. -/
  diagonal : ∀ p : Sentence, ∃ d : Sentence,
    Prov (imp d (imp (box d) p)) ∧ Prov (imp (imp (box d) p) d)

namespace ProvabilitySystem

variable (S : ProvabilitySystem.{u})

/-- Every sentence provably implies itself. -/
theorem prov_imp_self (p : S.Sentence) : S.Prov (S.imp p p) :=
  S.mp (S.mp (S.ax_S p (S.imp p p) p) (S.ax_K p (S.imp p p))) (S.ax_K p p)

variable {S}

/-- Weakening: from `⊢ q` infer `⊢ p → q`. -/
theorem prov_imp_of_prov {p q : S.Sentence} (h : S.Prov q) : S.Prov (S.imp p q) :=
  S.mp (S.ax_K q p) h

/-- Distribution of a hypothesis: from `⊢ p → (q → r)` and `⊢ p → q` infer `⊢ p → r`. -/
theorem prov_imp_dist {p q r : S.Sentence}
    (h₁ : S.Prov (S.imp p (S.imp q r))) (h₂ : S.Prov (S.imp p q)) :
    S.Prov (S.imp p r) :=
  S.mp (S.mp (S.ax_S p q r) h₁) h₂

/-- Transitivity of provable implication. -/
theorem prov_imp_trans {p q r : S.Sentence}
    (h₁ : S.Prov (S.imp p q)) (h₂ : S.Prov (S.imp q r)) :
    S.Prov (S.imp p r) :=
  prov_imp_dist (prov_imp_of_prov h₂) h₁

end ProvabilitySystem

/-- **Löb's theorem.**  In any provability system — in particular for Peano Arithmetic
with its arithmetized provability predicate, which satisfies the Hilbert–Bernays–Löb
derivability conditions and the diagonal lemma — if the theory proves `□φ → φ`, then the
theory proves `φ`.

Symbolically: if `PA ⊢ (Prov_PA(⌜φ⌝) → φ)` then `PA ⊢ φ`. -/
theorem Loeb_theorem (S : ProvabilitySystem.{u}) (φ : S.Sentence)
    (h : S.Prov (S.imp (S.box φ) φ)) : S.Prov φ := by
  -- Gödel fixed point: `⊢ d ↔ (□d → φ)`.
  obtain ⟨d, hd₁, hd₂⟩ := S.diagonal φ
  -- `⊢ □(d → (□d → φ))` by necessitation (D1).
  have a1 : S.Prov (S.box (S.imp d (S.imp (S.box d) φ))) := S.D1 hd₁
  -- `⊢ □d → □(□d → φ)` by D2.
  have a2 : S.Prov (S.imp (S.box d) (S.box (S.imp (S.box d) φ))) :=
    S.mp (S.D2 _ _) a1
  -- `⊢ □d → (□□d → □φ)`, again by D2.
  have a4 : S.Prov (S.imp (S.box d) (S.imp (S.box (S.box d)) (S.box φ))) :=
    ProvabilitySystem.prov_imp_trans a2 (S.D2 _ _)
  -- `⊢ □d → □□d` by D3, hence `⊢ □d → □φ`.
  have a6 : S.Prov (S.imp (S.box d) (S.box φ)) :=
    ProvabilitySystem.prov_imp_dist a4 (S.D3 d)
  -- With the hypothesis `⊢ □φ → φ` this gives `⊢ □d → φ`.
  have a7 : S.Prov (S.imp (S.box d) φ) := ProvabilitySystem.prov_imp_trans a6 h
  -- The fixed point now yields `⊢ d`, hence `⊢ □d` by necessitation, hence `⊢ φ`.
  exact S.mp a7 (S.D1 (S.mp hd₂ a7))

/-!
## Non-vacuity

The hypotheses of `ProvabilitySystem` are consistent, and are satisfied by systems in
which `Prov` is a proper subset of the sentences.  Here is a two-element model: sentences
are booleans, `imp` is boolean implication, `box` is constantly `true`, and `Prov p` says
`p = true`.  Note `¬ Prov false`, so the provability judgement is non-trivial.
-/

/-- A concrete model of `ProvabilitySystem` witnessing that the axioms are consistent and
that `Prov` need not hold of every sentence. -/
def boolSystem : ProvabilitySystem.{0} where
  Sentence := Bool
  imp p q := !p || q
  box _ := true
  Prov p := p = true
  mp := by decide +kernel
  ax_K := by decide +kernel
  ax_S := by decide +kernel
  D1 := by decide +kernel
  D2 := by decide +kernel
  D3 := by decide +kernel
  diagonal p := ⟨p, by cases p <;> rfl, by cases p <;> rfl⟩

/-- In the model `boolSystem` the provability judgement is not trivial: `false` is not
provable.  Hence `Frontier.Loeb_theorem` is not vacuously true. -/
theorem boolSystem_not_prov_false : ¬ boolSystem.Prov false := by
  intro h
  exact Bool.noConfusion (show (false : Bool) = true from h)

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

