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

lemma fv_subst0 {s : Trm} : ∀ (φ : Fml), (subst0 s φ).fv ⊆ φ.fv.erase 0 ∪ s.fv
  | eq t u => by
      intro x hx
      simp only [subst0, fv, Finset.mem_union] at hx
      rcases hx with hx | hx
      · have h1 := Trm.fv_subst0 s t hx
        simp only [Finset.mem_union, Finset.mem_erase, fv] at h1 ⊢
        tauto
      · have h1 := Trm.fv_subst0 s u hx
        simp only [Finset.mem_union, Finset.mem_erase, fv] at h1 ⊢
        tauto
  | not φ => fv_subst0 φ
  | and φ ψ => by
      intro x hx
      simp only [subst0, fv, Finset.mem_union] at hx
      rcases hx with hx | hx
      · have h1 := fv_subst0 (s := s) φ hx
        simp only [Finset.mem_union, Finset.mem_erase, fv] at h1 ⊢
        tauto
      · have h1 := fv_subst0 (s := s) ψ hx
        simp only [Finset.mem_union, Finset.mem_erase, fv] at h1 ⊢
        tauto
  | all i φ => by
      intro x hx
      by_cases hi : i = 0
      · subst hi
        simp only [subst0, if_pos rfl, fv, Finset.mem_erase] at hx
        simp only [Finset.mem_union, Finset.mem_erase, fv]
        tauto
      · simp only [subst0, if_neg hi, fv, Finset.mem_erase] at hx
        have h1 := fv_subst0 (s := s) φ hx.2
        simp only [Finset.mem_union, Finset.mem_erase, fv] at h1 ⊢
        tauto
  | subst n φ => by
      intro x hx
      simp only [subst0, fv, Finset.mem_erase] at hx
      simp only [Finset.mem_union, Finset.mem_erase, fv]
      tauto

/-- Gödel numbering of formulas. -/
