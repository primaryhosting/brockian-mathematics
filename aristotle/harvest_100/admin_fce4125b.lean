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
def neg (a : Form) : Form := a ⟶ Form.bot

end Form

open Form

/-- `Prov φ` means `PA ⊢ φ`.  The clauses are exactly the properties of the
provability relation of `PA` that Löb's argument uses: closure of provability
under the rules of a classical Hilbert calculus (`ax_k`, `ax_s`, `ax_dne`, `mp`),
and the Hilbert–Bernays–Löb derivability conditions
(`nec`: `PA ⊢ φ` implies `PA ⊢ □φ`;
`ax_distr`: `PA ⊢ □(φ → ψ) → (□φ → □ψ)`;
`ax_four`: `PA ⊢ □φ → □□φ`). -/
inductive Prov : Form → Prop
  | ax_k (a b : Form) : Prov (a ⟶ (b ⟶ a))
  | ax_s (a b c : Form) : Prov ((a ⟶ (b ⟶ c)) ⟶ ((a ⟶ b) ⟶ (a ⟶ c)))
  | ax_dne (a : Form) : Prov (((a ⟶ Form.bot) ⟶ Form.bot) ⟶ a)
  | ax_distr (a b : Form) : Prov (□(a ⟶ b) ⟶ (□a ⟶ □b))
  | ax_four (a : Form) : Prov (□a ⟶ □□a)
  | mp {a b : Form} : Prov (a ⟶ b) → Prov a → Prov b
  | nec {a : Form} : Prov a → Prov (□a)

namespace Prov

variable {a b c : Form}

/-- Weakening: a provable sentence is implied by anything. -/
theorem imp_intro (h : Prov b) : Prov (a ⟶ b) :=
  Prov.mp (Prov.ax_k b a) h

/-- Modus ponens under a hypothesis. -/
theorem mp_under (h₁ : Prov (a ⟶ (b ⟶ c))) (h₂ : Prov (a ⟶ b)) : Prov (a ⟶ c) :=
  Prov.mp (Prov.mp (Prov.ax_s a b c) h₁) h₂

/-- Hypothetical syllogism. -/
theorem syll (h₁ : Prov (a ⟶ b)) (h₂ : Prov (b ⟶ c)) : Prov (a ⟶ c) :=
  mp_under (imp_intro h₂) h₁

/-- `φ → φ`. -/
theorem imp_id : Prov (a ⟶ a) :=
  mp_under (Prov.ax_k a (a ⟶ a)) (Prov.ax_k a a)

end Prov

/-- **Löb's theorem** for `PA`.

If `ψ` is a fixed point of the map `χ ↦ (□χ → φ)`, in the sense that `PA` proves
`ψ → (□ψ → φ)` and `(□ψ → φ) → ψ` — such a `ψ` exists for every `φ` by the
diagonal lemma — and if `PA ⊢ □φ → φ`, then `PA ⊢ φ`. -/
theorem Loeb_theorem (φ : Form) (hfix : ∃ ψ : Form, Prov (ψ ⟶ (□ψ ⟶ φ)) ∧
    Prov ((□ψ ⟶ φ) ⟶ ψ)) (hφ : Prov (□φ ⟶ φ)) : Prov φ := by
  obtain ⟨ψ, hfix₁, hfix₂⟩ := hfix
  -- `PA ⊢ □ψ → □(□ψ → φ)`
  have h1 : Prov (□ψ ⟶ □(□ψ ⟶ φ)) :=
    Prov.mp (Prov.ax_distr ψ (□ψ ⟶ φ)) (Prov.nec hfix₁)
  -- `PA ⊢ □ψ → (□□ψ → □φ)`
  have h2 : Prov (□ψ ⟶ (□(□ψ) ⟶ □φ)) := Prov.syll h1 (Prov.ax_distr (□ψ) φ)
  -- `PA ⊢ □ψ → □φ`, using the formalized `Σ₁`-completeness axiom `□ψ → □□ψ`
  have h3 : Prov (□ψ ⟶ □φ) := Prov.mp_under h2 (Prov.ax_four ψ)
  -- `PA ⊢ □ψ → φ`
  have h4 : Prov (□ψ ⟶ φ) := Prov.syll h3 hφ
  -- hence `PA ⊢ ψ`, and by necessitation `PA ⊢ □ψ`
  have h5 : Prov ψ := Prov.mp hfix₂ h4
  exact Prov.mp h4 (Prov.nec h5)

/-!
## Non-triviality

The deductive system above is consistent, so `Frontier.Loeb_theorem` is not a
statement about a degenerate provability relation.  Interpreting every atom and
every boxed sentence as `True` and `bot` as `False` validates all the axioms and
rules of `Prov`, hence `PA ⊬ ⊥`.
-/

/-- An interpretation validating every axiom and rule of `Prov`, sending `bot` to
`False`. -/
def triv : Form → Prop
  | Form.atom _ => True
  | Form.bot => False
  | Form.imp a b => triv a → triv b
  | Form.box _ => True

theorem triv_of_prov {a : Form} (h : Prov a) : triv a := by
  induction h with
  | ax_k a b => exact fun ha _ => ha
  | ax_s a b c => exact fun h₁ h₂ ha => h₁ ha (h₂ ha)
  | ax_dne a => exact fun h => Classical.byContradiction h
  | ax_distr a b => exact fun _ _ => trivial
  | ax_four a => exact fun _ => trivial
  | mp _ _ ih₁ ih₂ => exact ih₁ ih₂
  | nec _ _ => exact trivial

/-- The provability relation is consistent: `PA ⊬ ⊥`. -/
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

