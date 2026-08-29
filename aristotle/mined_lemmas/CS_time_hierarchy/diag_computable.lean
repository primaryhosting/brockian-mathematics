import Mathlib

/-!
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

/-!
## Setup

We work with the standard Mathlib model of computation: partial recursive functions
presented by codes (`Nat.Partrec.Code`), together with the step-indexed evaluation
function `Nat.Partrec.Code.evaln : ℕ → Code → ℕ → Option ℕ`.  `evaln k c n` runs the
machine `c` on input `n` for `k` steps, returning `some v` if it halts with output `v`
within that budget and `none` otherwise.

A *language* is a decidable subset of `ℕ`, represented as a function `ℕ → Bool`, and
`DTIME t` is the class of languages decided by some machine within `t n` steps on
input `n`.

The time hierarchy theorem then says: for every computable time bound `t` there is a
larger time bound `t'` with `DTIME t ⊊ DTIME t'`, i.e. more time gives strictly more
languages.  The separating language is the diagonal language.
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- A language: a decision predicate on the natural numbers. -/
abbrev Language := ℕ → Bool

/-- `DTIME t` is the class of languages `L` for which there is a machine (code) that,
on every input `n`, halts within `t n` steps and outputs `1` if `n ∈ L` and `0`
otherwise. -/

theorem diag_computable (t : ℕ → ℕ) (ht : Computable t) : Computable (diag t) := by
  have h1 : Computable (fun n => evaln (t n) (Denumerable.ofNat Code n) n) :=
    Nat.Partrec.Code.primrec_evaln.to_comp.comp
      ((ht.pair (Primrec.ofNat Code).to_comp).pair Computable.id)
  have hEq : Computable (fun p : Option ℕ × Option ℕ => decide (p.1 = p.2)) := by
    obtain ⟨_, h⟩ := Primrec.eq (α := Option ℕ)
    exact h.to_comp.of_eq (fun p => by congr)
  have h2 : Computable
      (fun n => decide (evaln (t n) (Denumerable.ofNat Code n) n = some 1)) :=
    hEq.comp (h1.pair (Computable.const (some 1)))
  exact (Primrec.not.to_comp.comp h2).of_eq (fun n => by simp [diag, decide_not])

/-- Every computable language lies in `DTIME t'` for some (not necessarily computable)
time bound `t'`: simply take enough steps on each input. -/
