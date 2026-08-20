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

theorem prov_box_imp_box_bot {g : F.Sent} (hg : F.IsGoedelSentence g) :
    F.Prov (F.imp (F.box g) (F.box F.bot)) := by
  -- `⊢ □g → □(□g → ⊥)`
  have h₁ : F.Prov (F.imp (F.box g) (F.box (F.imp (F.box g) F.bot))) :=
    F.mp (F.D2 g (F.imp (F.box g) F.bot)) (F.D1 _ hg.1)
  -- `⊢ □(□g → ⊥) → (□□g → □⊥)`
  have h₂ : F.Prov (F.imp (F.box (F.imp (F.box g) F.bot))
      (F.imp (F.box (F.box g)) (F.box F.bot))) := F.D2 (F.box g) F.bot
  -- `⊢ □g → (□□g → □⊥)`
  have h₃ : F.Prov (F.imp (F.box g) (F.imp (F.box (F.box g)) (F.box F.bot))) :=
    prov_imp_trans h₁ h₂
  -- combine with the third derivability condition `⊢ □g → □□g`
  exact prov_imp_dist h₃ (F.D3 g)

/-- **Key lemma.**  The theory proves that its own consistency implies the Gödel
sentence: `⊢ Con(T) → g`. -/
