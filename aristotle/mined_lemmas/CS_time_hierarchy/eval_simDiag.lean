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

theorem eval_simDiag {t b : Nat → Nat} {pt : Nat} (hpt : ∀ x, eval (b x) pt x = some (t x))
    (x : Nat) {m : Nat} (hm : t x + b x + 4 ≤ m) :
    eval m (simDiag pt) x = some (encOpt (eval (t x) x x)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 4 := ⟨m - 4, by omega⟩
  have hinner : eval (s + 2) (cPairC cId cId) x = some (pair x x) :=
    eval_cPairC (eval_cId _ _) (eval_cId _ _)
  have hpt' : eval (s + 2) pt x = some (t x) := eval_mono (by omega) (hpt x)
  have hargs : eval (s + 3) (cPairC pt (cPairC cId cId)) x = some (pair (t x) (pair x x)) :=
    eval_cPairC hpt' hinner
  have hsim : eval (s + 3) cSim (pair (t x) (pair x x)) = some (encOpt (eval (t x) x x)) :=
    eval_cSim (by omega)
  exact eval_cComp hargs hsim

