import Mathlib
/-!
# Loeb Theorem
Category: Frontier — Set Theory
Target: Frontier.Loeb_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Löb's theorem: if `PA ⊢ (□φ → φ)` then `PA ⊢ φ`.

The statement is formalized for an arbitrary formal system satisfying the
Hilbert–Bernays–Löb derivability conditions together with the diagonal
(fixed-point) lemma, all of which hold for Peano Arithmetic with `□` the
standard provability predicate.  This is packaged in the structure
`Frontier.ProvabilitySystem` below, whose fields are:

* a type `Sent` of sentences, with an implication connective `imp` and a
  provability-predicate former `box` (`box φ` is the arithmetized sentence
  "`φ` is provable");
* a predicate `Prv` on sentences (`Prv φ` means "PA ⊢ φ");
* the propositional axiom schemes `K` and `S` for implication, plus modus
  ponens — i.e. `Prv` is closed under implicational propositional logic;
* the three derivability conditions: necessitation (D1), distribution (D2),
  and the formalized D1 (D3);
* the diagonal lemma, in the form needed for Löb's theorem: for every `φ`
  there is a sentence `ψ` for which PA proves `ψ ↔ (□ψ → φ)`.
-/

namespace Frontier

/-- An abstract formal system (think: Peano Arithmetic) equipped with a
provability predicate `box` satisfying the Hilbert–Bernays–Löb derivability
conditions and the diagonal lemma. -/
structure ProvabilitySystem where
  /-- The type of sentences of the system. -/
  Sent : Type
  /-- Implication connective. -/
  imp : Sent → Sent → Sent
  /-- Arithmetized provability: `box φ` is the sentence "`φ` is provable". -/
  box : Sent → Sent
  /-- `Prv φ` means "the system proves `φ`". -/
  Prv : Sent → Prop
  /-- Axiom scheme K of propositional logic. -/
  axK : ∀ a b, Prv (imp a (imp b a))
  /-- Axiom scheme S of propositional logic. -/
  axS : ∀ a b c, Prv (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  /-- Modus ponens: provability is closed under detachment. -/
  mp : ∀ {a b}, Prv (imp a b) → Prv a → Prv b
  /-- Derivability condition D1 (necessitation): if `⊢ φ` then `⊢ □φ`. -/
  D1 : ∀ {a}, Prv a → Prv (box a)
  /-- Derivability condition D2 (distribution): `⊢ □(φ → ψ) → (□φ → □ψ)`. -/
  D2 : ∀ a b, Prv (imp (box (imp a b)) (imp (box a) (box b)))
  /-- Derivability condition D3: `⊢ □φ → □□φ`. -/
  D3 : ∀ a, Prv (imp (box a) (box (box a)))
  /-- Diagonal lemma: for each `φ` there is `ψ` with `⊢ ψ ↔ (□ψ → φ)`. -/
  diag : ∀ a, ∃ p, Prv (imp p (imp (box p) a)) ∧ Prv (imp (imp (box p) a) p)

namespace ProvabilitySystem

variable (S : ProvabilitySystem)

/-- `⊢ φ → φ`. -/
theorem imp_self (a : S.Sent) : S.Prv (S.imp a a) :=
  S.mp (S.mp (S.axS a (S.imp a a) a) (S.axK a (S.imp a a))) (S.axK a a)

/-- If `⊢ b` then `⊢ a → b`. -/
theorem imp_intro {b : S.Sent} (a : S.Sent) (h : S.Prv b) : S.Prv (S.imp a b) :=
  S.mp (S.axK b a) h

/-- Syllogism: from `⊢ a → b` and `⊢ b → c` infer `⊢ a → c`. -/
theorem syll {a b c : S.Sent} (hab : S.Prv (S.imp a b)) (hbc : S.Prv (S.imp b c)) :
    S.Prv (S.imp a c) :=
  S.mp (S.mp (S.axS a b c) (S.imp_intro a hbc)) hab

/-- Distribution of a hypothesis: from `⊢ a → (b → c)` and `⊢ a → b` infer `⊢ a → c`. -/
theorem distrib {a b c : S.Sent} (h₁ : S.Prv (S.imp a (S.imp b c)))
    (h₂ : S.Prv (S.imp a b)) : S.Prv (S.imp a c) :=
  S.mp (S.mp (S.axS a b c) h₁) h₂

end ProvabilitySystem

/-- **Löb's theorem.**  In any formal system satisfying the Hilbert–Bernays–Löb
derivability conditions and the diagonal lemma (in particular, in Peano
Arithmetic with `□` the standard provability predicate): if the system proves
`□φ → φ`, then it proves `φ`. -/
theorem Loeb_theorem (S : ProvabilitySystem) (a : S.Sent)
    (h : S.Prv (S.imp (S.box a) a)) : S.Prv a := by
  obtain ⟨p, hfwd, hbwd⟩ := S.diag a
  -- `⊢ □p → □(□p → a)`
  have h1 : S.Prv (S.imp (S.box p) (S.box (S.imp (S.box p) a))) :=
    S.mp (S.D2 p (S.imp (S.box p) a)) (S.D1 hfwd)
  -- `⊢ □p → (□□p → □a)`
  have h2 : S.Prv (S.imp (S.box p) (S.imp (S.box (S.box p)) (S.box a))) :=
    S.syll h1 (S.D2 (S.box p) a)
  -- `⊢ □p → □a`
  have h3 : S.Prv (S.imp (S.box p) (S.box a)) := S.distrib h2 (S.D3 p)
  -- `⊢ □p → a`
  have h4 : S.Prv (S.imp (S.box p) a) := S.syll h3 h
  -- hence `⊢ p`, so `⊢ □p`, so `⊢ a`
  have h5 : S.Prv p := S.mp hbwd h4
  exact S.mp h4 (S.D1 h5)

/-- The hypotheses of `Frontier.Loeb_theorem` are satisfiable by a system in which
not every sentence is provable, so the theorem is not vacuous.  Here sentences are
booleans, `box` is the constantly-true sentence, and `Prv b` says `b = true`. -/
def boolSystem : ProvabilitySystem where
  Sent := Bool
  imp a b := (!a || b)
  box _ := true
  Prv b := b = true
  axK := by decide
  axS := by decide
  mp := by
    intro a b
    revert a b
    decide
  D1 := by decide
  D2 := by decide
  D3 := by decide
  diag a := ⟨a, by revert a; decide, by revert a; decide⟩


theorem boolSystem_not_trivial : ¬ boolSystem.Prv false := by
  simp [boolSystem]

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

