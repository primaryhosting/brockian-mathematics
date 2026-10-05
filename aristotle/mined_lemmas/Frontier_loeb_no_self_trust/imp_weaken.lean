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

/-- An abstract *provability structure*: a theory `T` over a type of sentences, equipped with
an implication connective, a provability predicate `Prf` ("`T` proves ..."), and an internal
provability operator `box` (the arithmetized provability predicate of `T`).

The axioms are:

* `mp` : the provable sentences are closed under modus ponens;
* `ax_K1`, `ax_K2` : the two Hilbert axiom schemes for implication, so that `T` contains
  (implicational) propositional logic;
* `nec` : necessitation — if `T` proves `A`, then `T` proves `□A`;
* `ax_K` : the distribution axiom `□(A → B) → (□A → □B)`;
* `ax_four` : `□A → □□A`;
* `diag` : the diagonal (fixed point) lemma: for every sentence `A` there is a sentence `F`
  with `T ⊢ F ↔ (□F → A)`.

These are exactly the Hilbert–Bernays–Löb derivability conditions together with the
diagonal lemma, all of which hold e.g. for Peano arithmetic and its provability predicate. -/
structure ProvabilityStructure where
  /-- The type of sentences of the language. -/
  Sent : Type*
  /-- Implication between sentences. -/
  imp : Sent → Sent → Sent
  /-- `Prf A` means: the theory proves the sentence `A`. -/
  Prf : Sent → Prop
  /-- `box A` is the sentence expressing "`A` is provable in the theory". -/
  box : Sent → Sent
  /-- Modus ponens. -/
  mp : ∀ {a b : Sent}, Prf (imp a b) → Prf a → Prf b
  /-- Hilbert axiom scheme `A → (B → A)`. -/
  ax_K1 : ∀ a b : Sent, Prf (imp a (imp b a))
  /-- Hilbert axiom scheme `(A → (B → C)) → ((A → B) → (A → C))`. -/
  ax_K2 : ∀ a b c : Sent, Prf (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  /-- Necessitation. -/
  nec : ∀ {a : Sent}, Prf a → Prf (box a)
  /-- Distribution axiom for the provability operator. -/
  ax_K : ∀ a b : Sent, Prf (imp (box (imp a b)) (imp (box a) (box b)))
  /-- Transparency of provability: `□A → □□A`. -/
  ax_four : ∀ a : Sent, Prf (imp (box a) (box (box a)))
  /-- Diagonal lemma. -/
  diag : ∀ a : Sent, ∃ f : Sent,
    Prf (imp f (imp (box f) a)) ∧ Prf (imp (imp (box f) a) f)

namespace ProvabilityStructure

variable (T : ProvabilityStructure)

/-- The derived rule: from `A → (B → C)` and `A → B` infer `A → C`. -/

theorem imp_weaken {a b : T.Sent} (h : T.Prf b) : T.Prf (T.imp a b) :=
  T.mp (T.ax_K1 b a) h

/-- Syllogism: from `A → B` and `B → C` infer `A → C`. -/
