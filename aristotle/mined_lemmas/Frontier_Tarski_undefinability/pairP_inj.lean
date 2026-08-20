/-
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment because Lean requires `import` before any
-- module docstring `/-! ... -/`.)

import Mathlib

/-!
## Overview

We formalize Tarski's undefinability theorem: the set of (Gödel numbers of) true
sentences of arithmetic is not itself definable by an arithmetical formula.

Everything is built from scratch:

* `Frontier.Tm` — terms of the language of arithmetic (variables, numerals, `+`, `*`);
* `Frontier.Fm` — formulas (equations, negation, conjunction, existential quantification);
* `Frontier.Tm.eval`, `Frontier.Fm.Sat` — the standard-model semantics over `ℕ`;
* `Frontier.Fm.freeVars` — free variables, so that "sentence" is meaningful;
* `Frontier.Fm.enc` — an injective Gödel numbering;
* `Frontier.TruthSet` — the set of Gödel numbers of true sentences of arithmetic;
* `Frontier.Definable` — definability of a set of naturals by an arithmetical formula.

The main theorem `Frontier.Tarski_undefinability` states `¬ Definable TruthSet`.
-/

namespace Frontier

/-! ### A polynomial pairing function -/

/-- A polynomial (twice-Cantor) pairing function on `ℕ`. -/

theorem pairP_inj {a b c d : ℕ} (h : pairP a b = pairP c d) : a = c ∧ b = d := by
  unfold pairP at h
  have hs : a + b = c + d := by
    rcases lt_trichotomy (a + b) (c + d) with h1 | h1 | h1
    · nlinarith
    · exact h1
    · nlinarith
  rw [hs] at h
  omega

/-! ### Syntax -/

/-- Terms of the language of arithmetic: variables, numerals, sums and products. -/
inductive Tm where
  | var : ℕ → Tm
  | num : ℕ → Tm
  | add : Tm → Tm → Tm
  | mul : Tm → Tm → Tm
deriving DecidableEq

/-- Formulas of the language of arithmetic: equations between terms, closed under
negation, conjunction and existential quantification. -/
inductive Fm where
  | eq : Tm → Tm → Fm
  | neg : Fm → Fm
  | and : Fm → Fm → Fm
  | ex : ℕ → Fm → Fm
deriving DecidableEq

/-! ### Semantics in the standard model `ℕ` -/

/-- Value of a term under an assignment of naturals to variables. -/
