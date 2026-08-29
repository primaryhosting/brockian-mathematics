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

lemma sat_subst0 {s : Trm} (hs : s.fv ⊆ {0}) : ∀ (φ : Fml) (ρ : ℕ → ℕ),
    (subst0 s φ).Sat ρ ↔ φ.Sat (Function.update ρ 0 (s.eval ρ))
  | eq t u, ρ => by
      simp only [subst0, Sat, Trm.eval_subst0 s ρ t, Trm.eval_subst0 s ρ u]
  | not φ, ρ => by simp [subst0, Sat, sat_subst0 hs φ ρ]
  | and φ ψ, ρ => by simp [subst0, Sat, sat_subst0 hs φ ρ, sat_subst0 hs ψ ρ]
  | all i φ, ρ => by
      by_cases hi : i = 0
      · subst hi
        simp only [subst0, if_pos rfl, Sat]
        refine forall_congr' (fun n => ?_)
        rw [Function.update_idem]
      · simp only [subst0, if_neg hi, Sat]
        refine forall_congr' (fun n => ?_)
        rw [sat_subst0 hs φ]
        have hev : s.eval (Function.update ρ i n) = s.eval ρ := by
          refine Trm.eval_congr s (fun j hj => ?_)
          have hj0 : j = 0 := by simpa using hs hj
          simp [hj0, Ne.symm hi]
        rw [hev, Function.update_comm (Ne.symm hi)]
  | subst n φ, ρ => by
      simp only [subst0, Sat]
      rw [Function.update_idem]

