/-!
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

This file is self-contained: it depends on nothing but the Lean core library.

We set up a concrete model of computation.  Inputs are natural numbers, programs are
natural numbers as well (a code is read as `pair tag args`, so that every natural number
is a program), and `eval k c x` runs the program `c` on input `x` with a budget of `k`
steps.  The instruction set contains the basic arithmetic and pairing operations, a
conditional, an unbounded loop, and one universal instruction which runs a given program
on a given input under a given step budget, at the cost of that budget plus one step.

`InTime t L` says that the language `L : Nat → Bool` is decided by some program within
`t x` steps on every input `x`.  Since running a program with more fuel gives the same
result (`eval_mono`), these classes grow with `t`.

The main result `CS.time_hierarchy` is the time hierarchy theorem for this model: if the
time bound `t` is itself computable within time `b`, and `T x ≥ t x + b x + 8`, then
every language decidable in time `t` is decidable in time `T`, and some language --
the diagonal language `diagLang t` -- is decidable in time `T` but not in time `t`.
-/

namespace CS

/-! ## A pairing function on `Nat` -/

/-- `twos d` is the 2-adic valuation of `d` (with `twos 0 = 0`). -/

theorem eval_succ : ∀ (k c x v : Nat), eval k c x = some v → eval (k + 1) c x = some v := by
  intro k
  induction k with
  | zero => intro c x v hv; rw [eval_zero] at hv; exact absurd hv (by simp)
  | succ k ih =>
    intro c x v hv
    rw [eval] at hv ⊢
    by_cases h0 : fst c = 0
    · simpa [h0] using hv
    by_cases h1 : fst c = 1
    · simpa [h0, h1] using hv
    by_cases h2 : fst c = 2
    · simpa [h0, h1, h2] using hv
    by_cases h3 : fst c = 3
    · simpa [h0, h1, h2, h3] using hv
    by_cases h4 : fst c = 4
    · simp only [h4, if_true] at hv ⊢
      cases hf : eval k (fst (snd c)) x with
      | none => rw [hf] at hv; simp at hv
      | some u =>
        cases hg : eval k (snd (snd c)) x with
        | none => rw [hf, hg] at hv; simp at hv
        | some w =>
          rw [hf, hg] at hv
          rw [ih _ _ _ hf, ih _ _ _ hg]
          simpa using hv
    by_cases h5 : fst c = 5
    · simpa [h0, h1, h2, h3, h4, h5] using hv
    by_cases h6 : fst c = 6
    · simpa [h0, h1, h2, h3, h4, h5, h6] using hv
    by_cases h7 : fst c = 7
    · simp only [h7, if_true] at hv ⊢
      cases hg : eval k (snd (snd c)) x with
      | none => rw [hg] at hv; simp at hv
      | some w =>
        rw [hg] at hv
        rw [ih _ _ _ hg]
        simpa using ih _ _ _ (by simpa using hv)
    by_cases h8 : fst c = 8
    · simp only [h8, if_true] at hv ⊢
      cases hf : eval k (fst (snd c)) x with
      | none => rw [hf] at hv; simp at hv
      | some w =>
        rw [hf] at hv
        rw [ih _ _ _ hf]
        simp only [Option.bind_some] at hv ⊢
        by_cases hw : w = 0
        · simp only [hw, if_true] at hv ⊢
          exact ih _ _ _ hv
        · simp only [hw, if_false] at hv ⊢
          exact ih _ _ _ hv
    by_cases h9 : fst c = 9
    · simp only [h9, if_true] at hv ⊢
      by_cases hx : x = 0
      · simpa [hx] using hv
      · simp only [hx, if_false] at hv ⊢
        cases hf : eval k (snd c) x with
        | none => rw [hf] at hv; simp at hv
        | some w =>
          rw [hf] at hv
          rw [ih _ _ _ hf]
          simpa using ih _ _ _ (by simpa using hv)
    by_cases h10 : fst c = 10
    · by_cases hk : fst x ≤ k
      · have hk' : fst x ≤ k + 1 := by omega
        simp only [h10, hk, hk', reduceIte, and_self] at hv ⊢
        exact hv
      · simp only [h10, hk, reduceIte, and_false] at hv
        exact absurd hv (by simp)
    · simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, if_false, false_and] at hv
      exact absurd hv (by simp)

