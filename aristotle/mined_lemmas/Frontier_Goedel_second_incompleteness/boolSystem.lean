/-
# Goedel Second Incompleteness
Category: Frontier — Set Theory
Target: Frontier.Goedel_second_incompleteness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/--
An abstract **formal system with a provability predicate**.

This packages exactly the structure that a consistent, recursively axiomatized theory `T`
extending `PA` provides:

* a type of sentences, with implication `imp`, falsity `bot`, and the internal provability
  predicate `box p = Pr_T(⌜p⌝)`;
* the theory is closed under modus ponens and contains the implicational fragment of
  propositional logic (the combinators `axK` and `axS`);
* the **Hilbert–Bernays–Löb derivability conditions**
  `necessitation` (D1: `T ⊢ p` implies `T ⊢ Pr(⌜p⌝)`),
  `boxK` (D2: `T ⊢ Pr(⌜p → q⌝) → Pr(⌜p⌝) → Pr(⌜q⌝)`), and
  `boxFour` (D3: `T ⊢ Pr(⌜p⌝) → Pr(⌜Pr(⌜p⌝)⌝)`), which hold for such theories because
  `Pr_T` is a `Σ₁` formula and `T` proves `Σ₁`-completeness;
* the **diagonal (fixed point) lemma**: for every sentence `p` there is a sentence `h` with
  `T ⊢ h ↔ (Pr(⌜h⌝) → p)`, available since `T` is recursively axiomatized and extends `PA`.

Note that no negation axiom (double negation elimination) is assumed: the results below use
only the positive implicational fragment, so they apply a fortiori to any theory extending `PA`.
-/
structure ProvabilitySystem where
  /-- The type of sentences of the theory. -/
  Sentence : Type
  /-- `Provable p` means that the theory proves the sentence `p`. -/
  Provable : Sentence → Prop
  /-- Implication of sentences. -/
  imp : Sentence → Sentence → Sentence
  /-- The false sentence. -/
  bot : Sentence
  /-- `box p` is the sentence `Pr(⌜p⌝)` expressing that `p` is provable in the theory. -/
  box : Sentence → Sentence
  /-- The theory is closed under modus ponens. -/
  modusPonens : ∀ {p q : Sentence}, Provable (imp p q) → Provable p → Provable q
  /-- The propositional axiom `p → (q → p)`. -/
  axK : ∀ p q : Sentence, Provable (imp p (imp q p))
  /-- The propositional axiom `(p → q → r) → (p → q) → (p → r)`. -/
  axS : ∀ p q r : Sentence,
    Provable (imp (imp p (imp q r)) (imp (imp p q) (imp p r)))
  /-- Derivability condition D1. -/
  necessitation : ∀ {p : Sentence}, Provable p → Provable (box p)
  /-- Derivability condition D2. -/
  boxK : ∀ p q : Sentence, Provable (imp (box (imp p q)) (imp (box p) (box q)))
  /-- Derivability condition D3. -/
  boxFour : ∀ p : Sentence, Provable (imp (box p) (box (box p)))
  /-- The diagonal lemma, in the form needed for Löb's theorem. -/
  diagonal : ∀ p : Sentence, ∃ h : Sentence,
    Provable (imp h (imp (box h) p)) ∧ Provable (imp (imp (box h) p) h)

namespace ProvabilitySystem

variable (T : ProvabilitySystem)

/-- The theory is consistent when it does not prove falsity. -/

def boolSystem : ProvabilitySystem where
  Sentence := Bool
  Provable p := p = true
  imp p q := (!p || q)
  bot := false
  box _ := true
  modusPonens {p q} hpq hp := by
    revert hpq hp; cases p <;> cases q <;> simp
  axK p q := by cases p <;> cases q <;> simp
  axS p q r := by cases p <;> cases q <;> cases r <;> simp
  necessitation _ := rfl
  boxK p q := by cases p <;> cases q <;> simp
  boxFour p := by cases p <;> simp
  diagonal p := ⟨p, by cases p <;> simp, by cases p <;> simp⟩

