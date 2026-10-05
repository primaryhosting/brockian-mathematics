/-!
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is self-contained (no imports): a Lean module doc comment has to precede any
`import` command, and the required header above is a module doc comment, so the
development below is built from Lean core only.

We fix a small but genuine machine model: a step-indexed interpreter `run` for programs
coded by natural numbers, define the time-bounded classes `TIME t`, and prove by
diagonalization that allowing one extra step strictly increases the family of decidable
languages.
-/

namespace CS

/-- Inputs are pairs of natural numbers: the first component is read as (the code of) a
program, the second one as a clock. -/
abbrev Input : Type := Nat × Nat

/-- A *language* is a decidable predicate on inputs. -/
abbrev Lang : Type := Input → Bool

/--
`run s e x` runs the program with code `e` on input `x` for at most `s` steps.
It returns `some b` if the program halts within `s` steps with output `b`, and `none` if
it has not halted yet.

A program code `e : Nat` is decoded as an opcode `e % 3` together with an argument `e / 3`:

* opcode `0`: the constant program, outputting `true` iff its argument is `1`;
* opcode `1`: negation — run the subprogram whose code is the argument and flip the
  answer, at the cost of one extra step;
* opcode `2`: the *clocked diagonalizer* — on input `x = (a, k)` simulate the program with
  code `a` on the very same input `x` for `k + 1` steps and flip its answer, answering
  `true` if the simulated program has not halted in time.  The simulation is step for
  step, with one extra step of overhead.
-/

theorem run_succ : ∀ (s e : Nat) (x : Input) (b : Bool), run s e x = some b →
    run (s + 1) e x = some b := by
  intro s
  induction s with
  | zero => intro e x b h; rw [run_zero] at h; exact absurd h (by simp)
  | succ m ih =>
    intro e x b h
    have hm : e % 3 = 0 ∨ e % 3 = 1 ∨ e % 3 = 2 := by omega
    rcases hm with hmod | hmod | hmod
    · rw [run_op0 _ _ _ hmod] at h ⊢; exact h
    · rw [run_op1 _ _ _ hmod] at h ⊢
      rcases hc : run m (e / 3) x with _ | c
      · rw [hc] at h; simp at h
      · rw [ih _ _ _ hc]; rw [hc] at h; exact h
    · rcases hc : run (min m (x.2 + 1)) x.1 x with _ | c
      · rw [run_op2_none _ _ _ hmod hc] at h
        by_cases hkm : x.2 + 1 ≤ m
        · simp only [hkm, if_true] at h
          have hmin : min (m + 1) (x.2 + 1) = min m (x.2 + 1) := by omega
          rw [run_op2_none _ _ _ hmod (by rw [hmin]; exact hc)]
          simp [show x.2 + 1 ≤ m + 1 by omega, ← h]
        · simp only [hkm, if_false] at h; exact absurd h (by simp)
      · rw [run_op2_some _ _ _ hmod _ hc] at h
        have hmin : run (min (m + 1) (x.2 + 1)) x.1 x = some c := by
          by_cases hkm : x.2 + 1 ≤ m
          · have hmm : min (m + 1) (x.2 + 1) = min m (x.2 + 1) := by omega
            rw [hmm]; exact hc
          · have h1 : min m (x.2 + 1) = m := by omega
            have h2 : min (m + 1) (x.2 + 1) = m + 1 := by omega
            rw [h2]; exact ih _ _ _ (h1 ▸ hc)
        rw [run_op2_some _ _ _ hmod _ hmin]; exact h

/-- The answer of a halted computation is stable under increasing the step bound. -/
