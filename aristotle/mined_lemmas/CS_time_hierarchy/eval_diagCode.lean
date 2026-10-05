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

theorem eval_diagCode {t b : Nat → Nat} {pt : Nat} (hpt : ∀ x, eval (b x) pt x = some (t x))
    (x : Nat) {m : Nat} (hm : t x + b x + 8 ≤ m) :
    eval m (diagCode pt) x = some (if diagLang t x then 1 else 0) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, i = s + 1 := ⟨i - 1, by omega⟩
  have hS : ∀ n, t x + b x + 4 ≤ n → eval n (simDiag pt) x = some (encOpt (eval (t x) x x)) :=
    fun n hn => eval_simDiag hpt x hn
  have hP : ∀ n, t x + b x + 5 ≤ n →
      eval n (cComp cPred (simDiag pt)) x = some (encOpt (eval (t x) x x) - 1) := by
    intro n hn
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 2 := ⟨n - 2, by omega⟩
    exact eval_cComp (hS (p + 1) (by omega)) (eval_cPred _ _)
  have hPP : ∀ n, t x + b x + 6 ≤ n →
      eval n (cComp cPred (cComp cPred (simDiag pt))) x =
        some (encOpt (eval (t x) x x) - 1 - 1) := by
    intro n hn
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 2 := ⟨n - 2, by omega⟩
    exact eval_cComp (hP (p + 1) (by omega)) (eval_cPred _ _)
  unfold diagCode diagLang
  cases he : eval (t x) x x with
  | none =>
      have h1 : eval (s + 2) (cComp cPred (simDiag pt)) x = some 0 := by
        rw [hP _ (by omega), he]; rfl
      simpa using eval_cIfz_zero h1 (eval_cConst _ _ _)
  | some v =>
      match v, he with
      | 0, he =>
          have h1 : eval (s + 2) (cComp cPred (simDiag pt)) x = some 0 := by
            rw [hP _ (by omega), he]; rfl
          simpa using eval_cIfz_zero h1 (eval_cConst _ _ _)
      | 1, he =>
          have h1 : eval (s + 2) (cComp cPred (simDiag pt)) x = some (0 + 1) := by
            rw [hP _ (by omega), he]; rfl
          have h2 : eval (s + 1) (cComp cPred (cComp cPred (simDiag pt))) x = some 0 := by
            rw [hPP _ (by omega), he]; rfl
          have h3 : eval (s + 2)
              (cIfz (cComp cPred (cComp cPred (simDiag pt))) (cConst 0) (cConst 1)) x = some 0 :=
            eval_cIfz_zero h2 (eval_cConst s 0 x)
          simpa using eval_cIfz_succ h1 h3
      | (v + 2), he =>
          have h1 : eval (s + 2) (cComp cPred (simDiag pt)) x = some (v + 1 + 1) := by
            rw [hP _ (by omega), he]; rfl
          have h2 : eval (s + 1) (cComp cPred (cComp cPred (simDiag pt))) x = some (v + 1) := by
            rw [hPP _ (by omega), he]; rfl
          have h3 : eval (s + 2)
              (cIfz (cComp cPred (cComp cPred (simDiag pt))) (cConst 0) (cConst 1)) x = some 1 :=
            eval_cIfz_succ h2 (eval_cConst s 1 x)
          simpa using eval_cIfz_succ h1 h3

/-! ## The time hierarchy theorem -/

/--
**Time hierarchy theorem.**  If the time bound `t` is itself computable within time `b`
(witnessed by the program `pt`), and `T` exceeds `t + b` by a constant, then the class of
languages decidable in time `T` strictly contains the class of languages decidable in
time `t`: every language decidable in time `t` is decidable in time `T`, and there is a
language (obtained by diagonalization) decidable in time `T` but not in time `t`.
-/
