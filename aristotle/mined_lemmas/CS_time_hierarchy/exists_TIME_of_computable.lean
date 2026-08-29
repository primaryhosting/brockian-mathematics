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

theorem exists_time_of_computable {L : Language} (hL : Computable L) :
    ∃ t' : ℕ → ℕ, L ∈ DTIME t' := by
  have hF : Computable (fun n => if L n then 1 else 0) :=
    (Computable.cond hL (Computable.const 1) (Computable.const 0)).of_eq
      (fun n => by cases L n <;> simp)
  obtain ⟨c, hcode⟩ :=
    Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hF.partrec)
  have key : ∀ n, ∃ k, (if L n then 1 else 0) ∈ evaln k c n := by
    intro n
    refine evaln_complete.mp ?_
    rw [hcode]
    simp
  refine ⟨fun n => Classical.choose (key n), c, fun n => ?_⟩
  exact Option.mem_def.mp (Classical.choose_spec (key n))

/-- **Time hierarchy theorem.**  For every computable time bound `t` there is a time
bound `t'` such that strictly more languages can be decided in time `t'` than in time
`t`: `DTIME t ⊊ DTIME t'`.  The witness separating the two classes is the diagonal
language `diag t`. -/
