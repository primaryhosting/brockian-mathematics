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

theorem sat_diagOf {θ : Fm} (v : ℕ → ℕ) :
    (diagOf θ).Sat v ↔
      ¬ θ.Sat (Function.update (Function.update v 1 (diagF (v 0))) 0 (diagF (v 0))) := by
  simp only [diagOf, Fm.Sat_neg, Fm.Sat_ex, Fm.Sat_and, not_exists]
  constructor
  · intro h hsat
    refine h (diagF (v 0)) ⟨?_, diagF (v 0), ?_, hsat⟩
    · rw [sat_deltaFm]
      simp
    · simp [Tm.eval]
  · intro h k hk
    obtain ⟨hd, m, hm, hsat⟩ := hk
    rw [sat_deltaFm] at hd
    simp only [Function.update_self,
      Function.update_of_ne (show (0 : ℕ) ≠ 1 by omega)] at hd
    simp only [Fm.Sat_eq, Tm.eval, Function.update_self,
      Function.update_of_ne (show (1 : ℕ) ≠ 0 by omega)] at hm
    subst hm
    subst hd
    exact h hsat

/-- **Tarski's undefinability theorem.**  Arithmetical truth — the set of Gödel numbers
of true sentences of arithmetic — is not arithmetically definable. -/
