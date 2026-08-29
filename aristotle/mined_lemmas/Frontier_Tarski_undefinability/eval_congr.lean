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

lemma eval_congr {ρ ρ' : ℕ → ℕ} : ∀ (t : Trm), (∀ i ∈ t.fv, ρ i = ρ' i) →
    t.eval ρ = t.eval ρ'
  | var i, h => h i (by simp [fv])
  | zero, _ => rfl
  | succ t, h => by simp [eval, eval_congr t h]
  | add t u, h => by
      simp only [eval]
      rw [eval_congr t (fun i hi => h i (by simp [fv, hi])),
        eval_congr u (fun i hi => h i (by simp [fv, hi]))]
  | mul t u, h => by
      simp only [eval]
      rw [eval_congr t (fun i hi => h i (by simp [fv, hi])),
        eval_congr u (fun i hi => h i (by simp [fv, hi]))]

/-- Substitution of the term `s` for the variable `v₀`. -/
