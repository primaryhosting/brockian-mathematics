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

theorem exists_goedelSentence : ∃ G, P.IsGoedelSentence G := P.diagonal P.bot

/-- **Gödel's first incompleteness theorem** (the unprovability half):
a consistent theory does not prove its Gödel sentence. -/
