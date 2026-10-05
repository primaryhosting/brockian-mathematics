/-!
# Loeb Theorem
Category: Frontier — Set Theory
Target: Frontier.Loeb_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Löb's theorem states: if `PA ⊢ (□φ → φ)` then `PA ⊢ φ`, where `□φ` abbreviates the
arithmetized provability statement `Prov(⌜φ⌝)`.

The proof of Löb's theorem uses exactly two ingredients about `PA`:

* the *Hilbert–Bernays–Löb derivability conditions*, i.e. that `PA` proves all
  propositional tautologies, is closed under modus ponens and necessitation
  (`PA ⊢ φ` implies `PA ⊢ □φ`), and proves the distribution axiom
  `□(φ → ψ) → (□φ → □ψ)` and the formalized `Σ₁`-completeness axiom `□φ → □□φ`;
* the *diagonal (fixed point) lemma*, which supplies, for each `φ`, a sentence `ψ`
  with `PA ⊢ ψ ↔ (□ψ → φ)`.

Accordingly we formalize the syntax of the language of sentences (propositional
connectives together with the provability operator `□`), and the deductive
apparatus for `PA` given by the derivability conditions, as the inductive predicate
`Frontier.Prov`.  This is the standard axiomatization of the provability logic of
`PA` (classical propositional logic plus the modal axioms `K` and `4`); every one of
its clauses is a theorem about `PA` proved by Gödel and Hilbert–Bernays.  The
diagonal lemma is taken as an explicit hypothesis of the theorem, since it is the
purely arithmetical input to the argument.

`Frontier.Loeb_theorem` is then the precise statement: for every sentence `φ`, if
some sentence `ψ` is a fixed point of `□· → φ` (i.e. `PA` proves both implications
of `ψ ↔ (□ψ → φ)`) and `PA ⊢ □φ → φ`, then `PA ⊢ φ`.
-/

namespace Frontier

/-- Sentences: propositional formulas built from atoms and falsity using
implication, together with the provability operator `box`, whose intended reading
is `box φ = Prov(⌜φ⌝)`, the arithmetized statement "`φ` is provable in `PA`". -/
inductive Form : Type
  | atom : ℕ → Form
  | bot : Form
  | imp : Form → Form → Form
  | box : Form → Form

namespace Form

/-- Implication. -/
scoped infixr:25 " ⟶ " => Form.imp
/-- Provability operator. -/
scoped prefix:max "□" => Form.box

/-- Negation, `¬φ := φ → ⊥`. -/

theorem not_prov_bot : ¬ Prov Form.bot := fun h => triv_of_prov h

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

