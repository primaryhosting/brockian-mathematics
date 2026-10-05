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

/-!
## An abstract formal theory with a provability predicate

We axiomatize the situation of Gödel–Löb: a formal theory `T` whose language contains
an implication connective `imp`, a *provability predicate* `box` (the internal, arithmetized
statement "this sentence is provable in `T`"), and an external predicate `Prov` recording which
sentences are theorems of `T`.

The assumed principles are exactly the standard ones:

* modus ponens, and the implicational Hilbert axioms `K` and `S`
  (so `T` proves every tautology of the implicational fragment and is closed under
  propositional implicational reasoning);
* the Hilbert–Bernays–Löb derivability conditions
  `D1` (necessitation), `D2` (internal modus ponens) and `D3` (internal `D1`);
* the diagonal (fixed point) lemma: every sentence `a` admits a Gödel sentence `L`
  provably equivalent to `box L → a`.
-/

/-- An abstract formal theory equipped with a provability predicate satisfying the
Hilbert–Bernays–Löb derivability conditions and the diagonal lemma. -/
structure ProvabilityTheory where
  /-- The type of sentences of the theory. -/
  Sentence : Type
  /-- Implication between sentences. -/
  imp : Sentence → Sentence → Sentence
  /-- The internal provability predicate: `box a` is the sentence "`a` is provable in `T`". -/
  box : Sentence → Sentence
  /-- `Prov a` holds iff `a` is a theorem of the theory. -/
  Prov : Sentence → Prop
  /-- Modus ponens. -/
  mp : ∀ {a b : Sentence}, Prov (imp a b) → Prov a → Prov b
  /-- The Hilbert axiom scheme `K`: `a → (b → a)`. -/
  axK : ∀ a b : Sentence, Prov (imp a (imp b a))
  /-- The Hilbert axiom scheme `S`: `(a → (b → c)) → ((a → b) → (a → c))`. -/
  axS : ∀ a b c : Sentence, Prov (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  /-- Derivability condition D1 (necessitation): if `a` is provable then so is `box a`. -/
  D1 : ∀ {a : Sentence}, Prov a → Prov (box a)
  /-- Derivability condition D2: `box (a → b) → (box a → box b)`. -/
  D2 : ∀ a b : Sentence, Prov (imp (box (imp a b)) (imp (box a) (box b)))
  /-- Derivability condition D3: `box a → box (box a)`. -/
  D3 : ∀ a : Sentence, Prov (imp (box a) (box (box a)))
  /-- The diagonal lemma: for every `a` there is a sentence `L` with `T ⊢ L ↔ (box L → a)`. -/
  diag : ∀ a : Sentence, ∃ L : Sentence,
    Prov (imp L (imp (box L) a)) ∧ Prov (imp (imp (box L) a) L)

namespace ProvabilityTheory

variable (T : ProvabilityTheory)

/-- A theory is *consistent* (here: nontrivial) if some sentence is not provable in it. -/

theorem boolTheoryWithBot_consistentBot : boolTheoryWithBot.ConsistentBot :=
  fun h => Bool.noConfusion h

/-- Non-vacuous instance of Gödel's second incompleteness theorem in the two-valued example. -/
