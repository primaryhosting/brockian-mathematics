import Mathlib

/-!
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Overview

The Immerman-Szelepcsényi theorem states that nondeterministic space is closed under
complement; for logarithmic space, `NL = coNL`.  Its content is the *inductive counting*
technique: a nondeterministic machine can, using only `O(log n)` workspace, verify that a
vertex is **not** reachable in the configuration graph of another nondeterministic machine.

This file formalises exactly that.  We fix a small nondeterministic imperative language
whose programs use a constant number of variables holding natural numbers bounded by the
number `m` of vertices of the graph they are run on (so `O(log m)` bits of workspace), and
which can inspect the graph only through the local edge test `edg a b` applied to two of
its variables.  We then exhibit **one fixed program** `CS.nonReach` -- a closed term, not
depending on the graph, on `m`, or on anything else -- and prove

* `CS.immerman_szelepcsenyi`: `nonReach` has an accepting run on a graph `E` with source
  `s` and target `t` if and only if `t` is *not* reachable from `s`;
* `CS.immerman_szelepcsenyi_machine`: consequently, for every nondeterministic machine `M`
  with a finite configuration space, `nonReach` run on the configuration graph of `M`
  accepts exactly when `M` rejects;
* `CS.nonReach_space`: all variables stay bounded by `m` throughout a run, and there are
  only `13` of them (`CS.env_card`), i.e. the complementing computation uses `O(log m)`
  space.

If `M` is a nondeterministic `O(log n)`-space machine on inputs of length `n`, its
configuration graph has `m = n^{O(1)}` vertices, so `log m = O(log n)`: the complementing
program is again a nondeterministic logarithmic-space computation.  This is `NL = coNL`.
-/

namespace CS

/-! ## A nondeterministic logarithmic-space machine model

A machine is a *program* in a tiny imperative language with a fixed, finite number of
variables.  Each variable holds a natural number bounded by `m`, the number of vertices of
the configuration graph the program is run on; hence each variable occupies `O(log m)` bits
and a whole configuration of the program (program point + variable values) occupies
`O(log m)` bits.  The program may inspect the graph only through the local test
`edge a b` on the values of two of its variables.

`Stmt.ch` is nondeterministic choice and `Stmt.guess` nondeterministically stores an
arbitrary value `≤ m` in a variable; `Stmt.fail` has no transition, so a computation
*accepts* exactly when a terminating execution exists.
-/

abbrev Var := Fin 13


theorem certLoop_complete {E : Fin m → Fin m → Bool} {i : ℕ} (hi : i ≤ m) :
    ∀ (n : ℕ) (f : ℕ → ℕ), (∀ j < n, edgeB E (f j) (f (j+1)) = true) →
      ∀ (a : Env), a vI = i → a vW = f 0 → a vJ + n ≤ i →
        ∃ a', Exec E certLoop a a' ∧ a' vW = f n := by
  intro n
  induction n with
  | zero =>
      intro f _ a hI hW hJ
      rcases Nat.lt_or_ge (a vJ) (a vI) with hlt | hge
      · refine ⟨upd a vJ (a vI), ?_, by simp +decide [hW]⟩
        refine Exec.whT (by simp +decide [evalCond, hlt]) (Exec.chR Exec.cpy) (Exec.whF ?_)
        simp +decide [evalCond]
      · exact ⟨a, Exec.whF (by simp +decide [evalCond]; omega), hW⟩
  | succ n ih =>
      intro f hf a hI hW hJ
      have hlt : a vJ < a vI := by omega
      have hedge : edgeB E (a vW) (f 1) = true := by rw [hW]; exact hf 0 (by omega)
      have hf1 : f 1 ≤ m := le_of_lt (edgeB_lt hedge).2
      have hbody : Exec E certBody a
          (upd (upd (upd a vT (f 1)) vW ((upd a vT (f 1)) vT)) vJ
            ((upd (upd a vT (f 1)) vW ((upd a vT (f 1)) vT)) vJ + 1)) := by
        refine Exec.chL (Exec.seq (Exec.guess hf1)
          (Exec.iteT ?_ (Exec.seq Exec.cpy (Exec.incr ?_))))
        · simpa +decide [evalCond] using hedge
        · simp +decide
          omega
      obtain ⟨a', hrun, hw'⟩ := ih (fun j => f (j+1)) (fun j hj => hf (j+1) (by omega))
        (upd (upd (upd a vT (f 1)) vW ((upd a vT (f 1)) vT)) vJ
            ((upd (upd a vT (f 1)) vW ((upd a vT (f 1)) vT)) vJ + 1))
        (by simp +decide [hI]) (by simp +decide) (by simp +decide; omega)
      exact ⟨a', Exec.whT (by simp +decide [evalCond, hlt]) hbody hrun, by simpa using hw'⟩

