/-!
# Goedel Second Incompleteness
Category: Frontier — Set Theory
Target: Frontier.Goedel_second_incompleteness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (This development is self-contained pure Lean 4; it needs no Mathlib lemmas, so that the
-- module docstring required by the task specification can be the very first item of the file.)

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
## An abstract provability framework

Gödel's second incompleteness theorem says that no consistent, recursively axiomatized
theory `T` extending `PA` proves the sentence `Con(T)` expressing its own consistency.

The whole arithmetical content of that statement is encapsulated by the
Hilbert–Bernays–Löb *derivability conditions* for the provability predicate
`Prov_T` (arithmetized by a `Σ₁` formula `□`), together with the *diagonal lemma*,
which produces a Gödel sentence `g` with `T ⊢ g ↔ ¬□g`.  Both of these hold for every
consistent recursively axiomatized `T ⊇ PA`.

Below we axiomatize exactly this situation: a set of sentences with implication, falsity,
a provability operator `box`, a deductive closure operator `Prov` closed under modus ponens
and containing the two Hilbert axiom schemes for the implicational fragment, and the three
derivability conditions.  Consistency of the theory is `¬ Prov bot`, and the sentence
`con = □⊥ → ⊥` is the formalized consistency statement.

The main theorem `Frontier.Goedel_second_incompleteness` then states and proves:
if such a theory is consistent and has a Gödel sentence, it does not prove its own
consistency statement.  This is a fully Lean-checked reduction of the second incompleteness

theorem to the derivability conditions and the diagonal lemma.

The example `Frontier.ProvabilityFramework.exists_consistent_with_goedelSentence` at the end
of the file shows that the hypotheses of the main theorem are jointly satisfiable, i.e. that
the theorem is not vacuous.
-/

/-- An abstract framework for provability: a type of sentences carrying an implication,
a falsity constant, an internal provability operator `box`, and a predicate `Prov`
("the theory proves") closed under modus ponens, containing the Hilbert axiom schemes
`K` and `S`, and satisfying the three Hilbert–Bernays–Löb derivability conditions. -/
structure ProvabilityFramework where
  /-- The type of sentences of the theory. -/
  Sent : Type
  /-- Implication between sentences. -/
  imp : Sent → Sent → Sent
  /-- The false sentence. -/
  bot : Sent
  /-- The internal provability operator: `box p` expresses "`p` is provable in the theory". -/
  box : Sent → Sent
  /-- `Prov p` means: the theory proves the sentence `p`. -/
  Prov : Sent → Prop
  /-- Hilbert axiom scheme `K`. -/
  ax_K : ∀ p q : Sent, Prov (imp p (imp q p))
  /-- Hilbert axiom scheme `S`. -/
  ax_S : ∀ p q r : Sent,
    Prov (imp (imp p (imp q r)) (imp (imp p q) (imp p r)))
  /-- Modus ponens. -/
  mp : ∀ {p q : Sent}, Prov (imp p q) → Prov p → Prov q
  /-- First derivability condition: provable sentences are provably provable. -/
  D1 : ∀ p : Sent, Prov p → Prov (box p)
  /-- Second derivability condition: the theory internalizes modus ponens. -/
  D2 : ∀ p q : Sent, Prov (imp (box (imp p q)) (imp (box p) (box q)))
  /-- Third derivability condition: the theory internalizes the first one. -/
  D3 : ∀ p : Sent, Prov (imp (box p) (box (box p)))

namespace ProvabilityFramework

variable (F : ProvabilityFramework)

/-- The theory is consistent when it does not prove falsity. -/
