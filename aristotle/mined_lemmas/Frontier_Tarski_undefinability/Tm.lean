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

theorem Tm.enc_injective : Function.Injective Tm.enc := by
  intro a
  induction a with
  | var n => intro b; cases b <;> simp [Tm.enc] <;> omega
  | num n => intro b; cases b <;> simp [Tm.enc] <;> omega
  | add p q ihp ihq =>
      intro b
      cases b with
      | var m => intro h; simp only [Tm.enc] at h; omega
      | num m => intro h; simp only [Tm.enc] at h; omega
      | add r s =>
          intro h; simp only [Tm.enc] at h
          have h' : pairP p.enc q.enc = pairP r.enc s.enc := by omega
          obtain ⟨h1, h2⟩ := pairP_inj h'
          rw [ihp h1, ihq h2]
      | mul r s => intro h; simp only [Tm.enc] at h; omega
  | mul p q ihp ihq =>
      intro b
      cases b with
      | var m => intro h; simp only [Tm.enc] at h; omega
      | num m => intro h; simp only [Tm.enc] at h; omega
      | add r s => intro h; simp only [Tm.enc] at h; omega
      | mul r s =>
          intro h; simp only [Tm.enc] at h
          have h' : pairP p.enc q.enc = pairP r.enc s.enc := by omega
          obtain ⟨h1, h2⟩ := pairP_inj h'
          rw [ihp h1, ihq h2]

