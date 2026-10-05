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

theorem diag_notMem_DTIME (t : ℕ → ℕ) : diag t ∉ DTIME t := by
  rintro ⟨c, hc⟩
  have hn : Denumerable.ofNat Code (Encodable.encode c) = c := Denumerable.ofNat_encode c
  have h := hc (Encodable.encode c)
  by_cases hd : diag t (Encodable.encode c) = true
  · have hne : evaln (t (Encodable.encode c)) c (Encodable.encode c) ≠ some 1 := by
      have := hd
      rw [diag, decide_eq_true_iff, hn] at this
      exact this
    rw [if_pos hd] at h
    exact hne h
  · simp only [Bool.not_eq_true] at hd
    have heq : evaln (t (Encodable.encode c)) c (Encodable.encode c) = some 1 := by
      have := hd
      rw [diag, decide_eq_false_iff_not, not_not, hn] at this
      exact this
    rw [if_neg (by simp [hd]), heq] at h
    exact absurd h (by simp)

/-- The diagonal language is computable, provided the time bound is. -/
