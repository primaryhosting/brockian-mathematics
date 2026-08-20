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

theorem definable_even : Definable {n : ℕ | ∃ k, n = 2 * k} := by
  refine ⟨.ex 1 (.eq (.var 0) (.mul (.num 2) (.var 1))), ?_, ?_⟩
  · intro x hx
    simp only [Fm.freeVars, Finset.mem_erase, Tm.vars, Finset.mem_union,
      Finset.mem_singleton] at hx
    simp only [Finset.mem_singleton]
    rcases hx with ⟨hx1, hx2 | hx2⟩
    · exact hx2
    · simp only [Finset.notMem_empty, false_or] at hx2
      omega
  · intro n
    simp only [Fm.Sat_ex, Fm.Sat_eq, Tm.eval, Function.update_self,
      Function.update_of_ne (show (0 : ℕ) ≠ 1 by omega), Set.mem_setOf_eq]

/-- The truth set is nonempty: the true sentence `0 = 0` belongs to it. -/
