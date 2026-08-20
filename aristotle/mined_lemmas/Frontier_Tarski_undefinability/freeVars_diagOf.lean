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

theorem freeVars_diagOf {θ : Fm} (hθ : θ.freeVars ⊆ {0}) :
    (diagOf θ).freeVars ⊆ {0} := by
  intro x hx
  simp only [diagOf, Fm.freeVars, freeVars_deltaFm, Finset.mem_erase, Finset.mem_union,
    Tm.vars] at hx
  simp only [Finset.mem_singleton]
  rcases hx with ⟨hx1, hx2⟩
  rcases hx2 with hx2 | hx2
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
    omega
  · rcases hx2 with ⟨hx0, hx2⟩
    rcases hx2 with hx2 | hx2
    · simp only [Finset.mem_singleton] at hx2
      omega
    · have := hθ hx2
      simpa using this

