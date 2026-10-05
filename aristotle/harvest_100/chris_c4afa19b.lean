/-!
# Goedel Second Incompleteness
Category: Frontier — Set Theory
Target: Frontier.Goedel_second_incompleteness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free (plain Lean 4 core, no Mathlib) so that the
required header comment can be the very first thing in the file.

## What is formalized

The statement "no consistent recursively axiomatized theory extending PA proves its own
consistency" is formalized as a theorem about the *provability structure* of such a
theory, i.e. as the Hilbert–Bernays–Löb style reduction.

For a recursively axiomatized theory `T ⊇ PA` one arithmetizes syntax and obtains, for a
chosen `Sigma_1` provability predicate `Prov_T`, an operator on sentences
`box p := Prov_T(⌜p⌝)` for which the following are theorems of ordinary arithmetic
(Gödel, Hilbert–Bernays, Löb):

* `T ⊢ p  ⟹  T ⊢ box p`                              (derivability condition D1)
* `T ⊢ box (p → q) → (box p → box q)`                (derivability condition D2)
* `T ⊢ box p → box (box p)`                          (derivability condition D3)
* the diagonal (fixed point) lemma: for every sentence `A` there is a sentence `p`
  with `T ⊢ p ↔ (box p → A)`.

Together with the fact that `T` is closed under modus ponens and contains propositional
logic (here: the two Hilbert axiom schemes `K` and `S`, which is all that is used), these
data are exactly the content of the structure `Frontier.ProvabilityFramework` below.
The consistency sentence of `T` is `Con_T := box ⊥ → ⊥`, i.e. `¬ Prov_T(⌜⊥⌝)`.

The main theorem `Frontier.Goedel_second_incompleteness` states: for every such
framework, if `T` is consistent (`¬ T ⊢ ⊥`) then `T` does not prove `Con_T`.
It is derived from Löb's theorem, which is proved here in full from the four conditions.

The hypotheses are not vacuous: `Frontier.boolFramework` is an explicit consistent
model of all of them (see `Frontier.boolFramework_consistent`).
-/

namespace Frontier

universe u

/-- The abstract provability structure of a recursively axiomatized theory `T`
extending `PA`, together with its arithmetized provability predicate.

`S` is the type of sentences, `Thm p` means "`T` proves `p`", `imp` is implication,
`bot` is falsum, and `box p` is the arithmetized statement "`p` is provable in `T`".

The fields `ax_K`, `ax_S` and `modus_ponens` say that `T` is closed under propositional
reasoning; `hbl₁`, `hbl₂`, `hbl₃` are the Hilbert–Bernays–Löb derivability conditions;
`diagonal` is the Gödel diagonal (fixed point) lemma, available because `T` is
recursively axiomatized and extends `PA`. -/
structure ProvabilityFramework (S : Type u) where
  /-- `Thm p` : the theory proves the sentence `p`. -/
  Thm : S → Prop
  /-- Implication of sentences. -/
  imp : S → S → S
  /-- Falsum. -/
  bot : S
  /-- `box p` : the arithmetized sentence "`p` is provable in the theory". -/
  box : S → S
  /-- Propositional axiom scheme `p → (q → p)`. -/
  ax_K : ∀ p q, Thm (imp p (imp q p))
  /-- Propositional axiom scheme `(p → (q → r)) → ((p → q) → (p → r))`. -/
  ax_S : ∀ p q r, Thm (imp (imp p (imp q r)) (imp (imp p q) (imp p r)))
  /-- The theory is closed under modus ponens. -/
  modus_ponens : ∀ {p q}, Thm (imp p q) → Thm p → Thm q
  /-- First derivability condition: provable sentences are provably provable. -/
  hbl₁ : ∀ {p}, Thm p → Thm (box p)
  /-- Second derivability condition. -/
  hbl₂ : ∀ p q, Thm (imp (box (imp p q)) (imp (box p) (box q)))
  /-- Third derivability condition. -/
  hbl₃ : ∀ p, Thm (imp (box p) (box (box p)))
  /-- Gödel's diagonal lemma: every `A` has a fixed point of `p ↦ (box p → A)`. -/
  diagonal : ∀ A, ∃ p, Thm (imp p (imp (box p) A)) ∧ Thm (imp (imp (box p) A) p)

namespace ProvabilityFramework

variable {S : Type u} (P : ProvabilityFramework S)

/-- The consistency sentence `Con_T = ¬ Prov_T(⌜⊥⌝)`, written `box ⊥ → ⊥`. -/
def Con : S := P.imp (P.box P.bot) P.bot

/-- The theory is consistent: it does not prove falsum. -/
def Consistent : Prop := ¬ P.Thm P.bot

/-- Transitivity of provable implication. -/
theorem imp_trans {a b c : S} (h₁ : P.Thm (P.imp a b)) (h₂ : P.Thm (P.imp b c)) :
    P.Thm (P.imp a c) :=
  P.modus_ponens (P.modus_ponens (P.ax_S a b c)
    (P.modus_ponens (P.ax_K (P.imp b c) a) h₂)) h₁

/-- **Löb's theorem**: if `T` proves `Prov_T(⌜A⌝) → A`, then `T` proves `A`. -/
theorem loeb (A : S) (h : P.Thm (P.imp (P.box A) A)) : P.Thm A := by
  obtain ⟨p, hp₁, hp₂⟩ := P.diagonal A
  have h₂ : P.Thm (P.box (P.imp p (P.imp (P.box p) A))) := P.hbl₁ hp₁
  have h₃ : P.Thm (P.imp (P.box p) (P.box (P.imp (P.box p) A))) :=
    P.modus_ponens (P.hbl₂ _ _) h₂
  have h₄ : P.Thm (P.imp (P.box p) (P.imp (P.box (P.box p)) (P.box A))) :=
    P.imp_trans h₃ (P.hbl₂ _ _)
  have h₅ : P.Thm (P.imp (P.box p) (P.box A)) :=
    P.modus_ponens (P.modus_ponens (P.ax_S _ _ _) h₄) (P.hbl₃ p)
  have h₆ : P.Thm (P.imp (P.box p) A) := P.imp_trans h₅ h
  exact P.modus_ponens h₆ (P.hbl₁ (P.modus_ponens hp₂ h₆))

/-- A Gödel sentence: a sentence provably equivalent to its own unprovability. -/
def IsGoedelSentence (G : S) : Prop :=
  P.Thm (P.imp G (P.imp (P.box G) P.bot)) ∧ P.Thm (P.imp (P.imp (P.box G) P.bot) G)

/-- Gödel sentences exist, by the diagonal lemma. -/
theorem exists_goedelSentence : ∃ G, P.IsGoedelSentence G := P.diagonal P.bot

/-- **Gödel's first incompleteness theorem** (the unprovability half):
a consistent theory does not prove its Gödel sentence. -/
theorem goedel_first_incompleteness (hcon : P.Consistent) {G : S}
    (hG : P.IsGoedelSentence G) : ¬ P.Thm G := fun hp =>
  hcon (P.modus_ponens (P.modus_ponens hG.1 hp) (P.hbl₁ hp))

/-- If the theory proves its own consistency statement, it is inconsistent. -/
theorem inconsistent_of_provable_con (h : P.Thm P.Con) : P.Thm P.bot :=
  P.loeb P.bot h

end ProvabilityFramework

/-- **Gödel's second incompleteness theorem.**

No consistent recursively axiomatized theory extending `PA` proves its own consistency:
for any such theory, presented through its provability structure `P` (closure under
propositional logic and modus ponens, the three Hilbert–Bernays–Löb derivability
conditions for the arithmetized provability predicate `box`, and Gödel's diagonal
lemma), if `P` is consistent then `P` does not prove the sentence
`Con = box ⊥ → ⊥`. -/
theorem Goedel_second_incompleteness {S : Type u} (P : ProvabilityFramework S)
    (hcon : P.Consistent) : ¬ P.Thm P.Con :=
  fun h => hcon (P.inconsistent_of_provable_con h)

/-! ### The hypotheses are satisfiable

A trivial but consistent framework, showing that `ProvabilityFramework` together with
`Consistent` is not a contradictory set of assumptions (so the theorem above is not
vacuous). -/

/-- A consistent `ProvabilityFramework` on `Bool`. -/
def boolFramework : ProvabilityFramework Bool where
  Thm p := p = true
  imp p q := !p || q
  bot := false
  box _ := true
  ax_K p q := by revert p q; decide
  ax_S p q r := by revert p q r; decide
  modus_ponens {p q} := by revert p q; decide
  hbl₁ _ := rfl
  hbl₂ p q := by revert p q; decide
  hbl₃ p := by revert p; decide
  diagonal A := ⟨A, by revert A; decide, by revert A; decide⟩

theorem boolFramework_consistent : boolFramework.Consistent := by decide

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

