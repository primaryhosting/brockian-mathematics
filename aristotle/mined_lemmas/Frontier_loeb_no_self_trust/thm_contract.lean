/-
# Loeb No Self Trust
Category: Frontier Mind
Target: Frontier.loeb_no_self_trust
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Loeb No Self Trust
Category: Frontier Mind
Target: Frontier.loeb_no_self_trust
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/--
An abstract *provability system*: a theory `T` together with a provability predicate
`box` (read `box a` as the sentence "`a` is provable in `T`", i.e. `Prov(⌜a⌝)`).

The data and axioms are exactly the standard ingredients of the Hilbert–Bernays–Löb
analysis of self-reference:

* `Sentence`, `imp`: the sentences of the language, with an implication connective;
* `Thm`: the theorems of `T` (`Thm a` means `T ⊢ a`);
* `mp`, `ax_K1`, `ax_K2`: `T` contains the implicational fragment of propositional
  logic (the axiom schemas `a → (b → a)` and `(a → (b → c)) → ((a → b) → (a → c))`)
  and is closed under modus ponens;
* `nec` (**D1**): if `T ⊢ a` then `T ⊢ Prov(⌜a⌝)`;
* `ax_distr` (**D2**): `T ⊢ Prov(⌜a → b⌝) → (Prov(⌜a⌝) → Prov(⌜b⌝))`;
* `ax_four` (**D3**): `T ⊢ Prov(⌜a⌝) → Prov(⌜Prov(⌜a⌝)⌝)`;
* `fixpoint`: the diagonal (Gödel fixed point) lemma — every sentence `a` admits a
  sentence `d` with `T ⊢ d ↔ (Prov(⌜d⌝) → a)`.

These conditions are satisfied, for instance, by any consistent r.e. extension of
Peano arithmetic with its canonical provability predicate.
-/
structure ProvabilitySystem where
  /-- The sentences of the language. -/
  Sentence : Type
  /-- The implication connective. -/
  imp : Sentence → Sentence → Sentence
  /-- The provability predicate, internalized as an operation on sentences:
  `box a` is the sentence `Prov(⌜a⌝)`. -/
  box : Sentence → Sentence
  /-- `Thm a` means that the theory proves `a`. -/
  Thm : Sentence → Prop
  /-- The theory is closed under modus ponens. -/
  mp : ∀ {a b : Sentence}, Thm (imp a b) → Thm a → Thm b
  /-- Propositional axiom schema `a → (b → a)`. -/
  ax_K1 : ∀ (a b : Sentence), Thm (imp a (imp b a))
  /-- Propositional axiom schema `(a → (b → c)) → ((a → b) → (a → c))`. -/
  ax_K2 : ∀ (a b c : Sentence),
    Thm (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  /-- Derivability condition D1 (necessitation). -/
  nec : ∀ {a : Sentence}, Thm a → Thm (box a)
  /-- Derivability condition D2 (internal modus ponens). -/
  ax_distr : ∀ (a b : Sentence), Thm (imp (box (imp a b)) (imp (box a) (box b)))
  /-- Derivability condition D3 (provable Σ₁-completeness for provability). -/
  ax_four : ∀ (a : Sentence), Thm (imp (box a) (box (box a)))
  /-- The diagonal lemma: every `a` has a fixed point `d` with `T ⊢ d ↔ (□d → a)`. -/
  fixpoint : ∀ (a : Sentence), ∃ d : Sentence,
    Thm (imp d (imp (box d) a)) ∧ Thm (imp (imp (box d) a) d)

namespace ProvabilitySystem

variable (P : ProvabilitySystem)

/-- A theory is *consistent* if it does not prove every sentence. -/

theorem thm_contract {a b c : P.Sentence} (h₁ : P.Thm (P.imp a (P.imp b c)))
    (h₂ : P.Thm (P.imp a b)) : P.Thm (P.imp a c) :=
  P.mp (P.mp (P.ax_K2 a b c) h₁) h₂

/--
**Löb's theorem.** If a theory satisfying the derivability conditions proves the
reflection principle `Prov(⌜a⌝) → a` for a sentence `a`, then it already proves `a`.
-/
