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

theorem Fm.enc_injective : Function.Injective Fm.enc := by
  intro a
  induction a with
  | eq s t =>
      intro b
      cases b with
      | eq s' t' =>
          intro h; simp only [Fm.enc] at h
          have h' : pairP s.enc t.enc = pairP s'.enc t'.enc := by omega
          obtain ⟨h1, h2⟩ := pairP_inj h'
          rw [Tm.enc_injective h1, Tm.enc_injective h2]
      | neg g => intro h; simp only [Fm.enc] at h; omega
      | and g g' => intro h; simp only [Fm.enc] at h; omega
      | ex n g => intro h; simp only [Fm.enc] at h; omega
  | neg f ih =>
      intro b
      cases b with
      | eq s' t' => intro h; simp only [Fm.enc] at h; omega
      | neg g => intro h; simp only [Fm.enc] at h; exact congrArg Fm.neg (ih (by omega))
      | and g g' => intro h; simp only [Fm.enc] at h; omega
      | ex n g => intro h; simp only [Fm.enc] at h; omega
  | and f g ihf ihg =>
      intro b
      cases b with
      | eq s' t' => intro h; simp only [Fm.enc] at h; omega
      | neg g' => intro h; simp only [Fm.enc] at h; omega
      | and p q =>
          intro h; simp only [Fm.enc] at h
          have h' : pairP f.enc g.enc = pairP p.enc q.enc := by omega
          obtain ⟨h1, h2⟩ := pairP_inj h'
          rw [ihf h1, ihg h2]
      | ex n g' => intro h; simp only [Fm.enc] at h; omega
  | ex n f ih =>
      intro b
      cases b with
      | eq s' t' => intro h; simp only [Fm.enc] at h; omega
      | neg g' => intro h; simp only [Fm.enc] at h; omega
      | and p q => intro h; simp only [Fm.enc] at h; omega
      | ex m g =>
          intro h; simp only [Fm.enc] at h
          have h' : pairP n f.enc = pairP m g.enc := by omega
          obtain ⟨h1, h2⟩ := pairP_inj h'
          rw [h1, ih h2]

/-! ### Arithmetical truth and definability -/

/-- The set of Gödel numbers of true sentences of arithmetic (arithmetical truth). -/
