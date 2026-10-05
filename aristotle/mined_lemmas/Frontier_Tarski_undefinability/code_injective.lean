/-
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 requires
-- module doc comments to appear *after* the `import` lines.)

import Mathlib

/-!
## Overview

We formalize Tarski's undefinability theorem: the set of (Gödel numbers of) true
arithmetical sentences is not definable by any arithmetical formula.

Everything is built from scratch:

* `Frontier.Tarski.Trm` : terms of the language of arithmetic `(0, S, +, ·)`,
  with variables indexed by `ℕ`;
* `Frontier.Tarski.Fml` : formulas, built from equations by negation,
  conjunction, universal quantification, and a *parameter* constructor
  `Fml.subst n φ`, which denotes `φ` with the numeral `n` substituted for the
  variable `v₀` (this constructor is eliminable, see `Fml.purify`);
* `Frontier.Tarski.Fml.Sat` : the standard satisfaction relation in the
  structure `ℕ`;
* `Frontier.Tarski.Fml.code` : an injective Gödel numbering
  (`Frontier.Tarski.Fml.code_injective`);
* `Frontier.Tarski.TruthSet` : the set of codes of true sentences;
* `Frontier.Tarski.Definable` : the sets of naturals definable by a formula.

The main theorem is `Frontier.Tarski_undefinability : ¬ Definable TruthSet`.
-/

namespace Frontier
namespace Tarski

/-! ## Syntax -/

/-- Terms of the language of arithmetic, with variables indexed by `ℕ`. -/
inductive Trm : Type
  | var : ℕ → Trm
  | zero : Trm
  | succ : Trm → Trm
  | add : Trm → Trm → Trm
  | mul : Trm → Trm → Trm
  deriving DecidableEq

namespace Trm

/-- Value of a term under an assignment `ρ` of naturals to the variables. -/

lemma code_injective : Function.Injective code := by
  intro φ
  induction φ with
  | eq t u =>
      intro w h; cases w <;> simp only [code] at h
      · case eq a b =>
          have hp : Nat.pair t.code u.code = Nat.pair a.code b.code := by omega
          have := congrArg Nat.unpair hp
          simp only [Nat.unpair_pair, Prod.mk.injEq] at this
          exact congrArg₂ eq (Trm.code_injective this.1) (Trm.code_injective this.2)
      · omega
      · omega
      · omega
      · omega
  | not φ ih =>
      intro w h; cases w <;> simp only [code] at h
      · omega
      · exact congrArg not (ih (by omega))
      · omega
      · omega
      · omega
  | and φ ψ ihφ ihψ =>
      intro w h; cases w <;> simp only [code] at h
      · omega
      · omega
      · case and a b =>
          have hp : Nat.pair (code φ) (code ψ) = Nat.pair (code a) (code b) := by omega
          have := congrArg Nat.unpair hp
          simp only [Nat.unpair_pair, Prod.mk.injEq] at this
          exact congrArg₂ and (ihφ this.1) (ihψ this.2)
      · omega
      · omega
  | all i φ ih =>
      intro w h; cases w <;> simp only [code] at h
      · omega
      · omega
      · omega
      · case all j a =>
          have hp : Nat.pair i (code φ) = Nat.pair j (code a) := by omega
          have := congrArg Nat.unpair hp
          simp only [Nat.unpair_pair, Prod.mk.injEq] at this
          rw [this.1, ih this.2]
      · omega
  | subst n φ ih =>
      intro w h; cases w <;> simp only [code] at h
      · omega
      · omega
      · omega
      · omega
      · case subst m a =>
          have hp : Nat.pair n (code φ) = Nat.pair m (code a) := by omega
          have := congrArg Nat.unpair hp
          simp only [Nat.unpair_pair, Prod.mk.injEq] at this
          rw [this.1, ih this.2]

/-! ### Eliminability of the parameter constructor -/

/-- A formula is *pure* if it does not use the parameter constructor `subst`,
i.e. it is a formula of the plain language of arithmetic. -/
