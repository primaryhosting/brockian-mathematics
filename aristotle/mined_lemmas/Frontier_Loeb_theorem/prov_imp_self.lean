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
