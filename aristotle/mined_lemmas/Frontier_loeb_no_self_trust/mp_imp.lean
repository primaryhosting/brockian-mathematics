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
An abstract *provability system*: a theory `T` presented by

* a type `Sentence` of sentences, closed under implication `imp`;
* a formalized provability predicate `box` (`box p` is the sentence "`p` is provable in `T`");
* the set `Prov` of sentences that `T` actually proves.

The axioms are the usual ones needed for Löb's theorem:

* `mp` : `Prov` is closed under modus ponens;
* `axK`, `axS` : `T` proves the two axiom schemes of implicational propositional logic
  (together with `mp` these give all of implicational logic);
* `nec` : the first Hilbert–Bernays–Löb derivability condition
  (if `T` proves `p`, then `T` proves that it proves `p`);
* `boxK` : the second derivability condition (internal modus ponens);
* `ax4` : the third derivability condition (provable Σ₁-completeness for `box`);
* `diag` : the diagonal (fixed point) lemma: for every sentence `p` there is a sentence `g`
  which `T` proves to be equivalent to "if `g` is provable then `p`".
-/
structure ProvabilitySystem where
  /-- The type of sentences of the theory. -/
  Sentence : Type
  /-- Implication between sentences. -/
  imp : Sentence → Sentence → Sentence
  /-- The formalized provability predicate: `box p` says "`p` is provable". -/
  box : Sentence → Sentence
  /-- The sentences actually provable in the theory. -/
  Prov : Sentence → Prop
  /-- Modus ponens. -/
  mp : ∀ {p q : Sentence}, Prov (imp p q) → Prov p → Prov q
  /-- The axiom scheme `p → (q → p)`. -/
  axK : ∀ p q : Sentence, Prov (imp p (imp q p))
  /-- The axiom scheme `(p → (q → r)) → ((p → q) → (p → r))`. -/
  axS : ∀ p q r : Sentence,
    Prov (imp (imp p (imp q r)) (imp (imp p q) (imp p r)))
  /-- First derivability condition (necessitation). -/
  nec : ∀ {p : Sentence}, Prov p → Prov (box p)
  /-- Second derivability condition: `□(p → q) → (□p → □q)`. -/
  boxK : ∀ p q : Sentence, Prov (imp (box (imp p q)) (imp (box p) (box q)))
  /-- Third derivability condition: `□p → □□p`. -/
  ax4 : ∀ p : Sentence, Prov (imp (box p) (box (box p)))
  /-- Diagonal lemma: a fixed point `g` for the formula `□(·) → p`. -/
  diag : ∀ p : Sentence, ∃ g : Sentence,
    Prov (imp g (imp (box g) p)) ∧ Prov (imp (imp (box g) p) g)

namespace ProvabilitySystem

variable (T : ProvabilitySystem)

/-- Distribution rule: from `⊢ p → (q → r)` and `⊢ p → q` infer `⊢ p → r`. -/

theorem mp_imp {p q r : T.Sentence} (h₁ : T.Prov (T.imp p (T.imp q r)))
    (h₂ : T.Prov (T.imp p q)) : T.Prov (T.imp p r) :=
  T.mp (T.mp (T.axS p q r) h₁) h₂

/-- Transitivity of provable implication. -/
