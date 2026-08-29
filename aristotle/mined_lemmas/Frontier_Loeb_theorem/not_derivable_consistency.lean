/-!
# Loeb Theorem
Category: Frontier — Set Theory
Target: Frontier.Loeb_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Löb's theorem: if `PA ⊢ (□φ → φ)` then `PA ⊢ φ`, where `□φ` denotes the arithmetized
provability statement `Prov_PA(⌜φ⌝)`.

The theorem is a consequence of exactly the following features of `PA` together with its
canonical provability predicate (this is the standard, and the only informative, way to
formalize it: the arithmetization of syntax plays no role in the argument beyond supplying
these facts):

* the provable sentences are closed under modus ponens and contain the axioms `K` and `S`
  of the implicational fragment of propositional logic;
* the Hilbert–Bernays–Löb derivability conditions:
  - `⊢ φ` implies `⊢ □φ` (necessitation / D1),
  - `⊢ □(φ → ψ) → (□φ → □ψ)` (D2),
  - `⊢ □φ → □□φ` (D3);
* the Gödel–Carnap diagonal lemma: for every sentence `φ` there is a sentence `ψ` with
  `⊢ ψ ↔ (□ψ → φ)`.

`Frontier.ProvabilitySystem` below packages precisely these data, and
`Frontier.Loeb_theorem` is Löb's theorem for any such system.

To show that the axioms are not vacuous, the second half of the file constructs a concrete,
consistent system `Frontier.Form` / `Frontier.Derivable` satisfying all of them (Section
`Concrete`), and derives from Löb's theorem the corresponding form of Gödel's second
incompleteness theorem.
-/

namespace Frontier

/-- A *provability system*: an abstract rendering of a theory such as `PA` together with its
provability predicate `□`.  The fields are the closure properties of `PA`-provability used in
Löb's argument: propositional logic (in the implicational fragment), the three
Hilbert–Bernays–Löb derivability conditions, and the diagonal lemma. -/
structure ProvabilitySystem where
  /-- The type of sentences of the theory. -/
  Sent : Type
  /-- Implication between sentences. -/
  imp : Sent → Sent → Sent
  /-- The provability operator: `box φ` is the arithmetized statement "`φ` is provable". -/
  box : Sent → Sent
  /-- `Prov φ` says that the theory proves `φ`. -/
  Prov : Sent → Prop
  /-- Axiom `K` of propositional logic. -/
  ax_k : ∀ a b, Prov (imp a (imp b a))
  /-- Axiom `S` of propositional logic. -/
  ax_s : ∀ a b c, Prov (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  /-- Modus ponens. -/
  mp : ∀ {a b}, Prov (imp a b) → Prov a → Prov b
  /-- Derivability condition D1 (necessitation). -/
  nec : ∀ {a}, Prov a → Prov (box a)
  /-- Derivability condition D2 (distribution of `box` over implication). -/
  dist : ∀ a b, Prov (imp (box (imp a b)) (imp (box a) (box b)))
  /-- Derivability condition D3 (provable `Σ₁`-completeness for provability statements). -/
  four : ∀ a, Prov (imp (box a) (box (box a)))
  /-- The diagonal lemma: for every `f` there is a sentence `p` provably equivalent to
  `box p → f`. -/
  diag : ∀ f, ∃ p, Prov (imp p (imp (box p) f)) ∧ Prov (imp (imp (box p) f) p)

namespace ProvabilitySystem

variable (S : ProvabilitySystem) {a b c : S.Sent}

/-- From `⊢ b` infer `⊢ a → b`. -/

theorem not_derivable_consistency : ¬ Derivable (.imp (.box .bot) .bot) := fun h =>
  Derivable_consistent (loeb Form.bot h)

end Concrete

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

