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


theorem exec_frame {E : Fin m → Fin m → Bool} {st : Stmt} {e e' : Env}
    (h : Exec E st e e') : ∀ x ∉ mods st, e' x = e x := by
  induction h with
  | skip => intro x _; rfl
  | zero => intro x hx; simp [mods] at hx; exact upd_ne _ _ hx
  | incr h => intro x hx; simp [mods] at hx; exact upd_ne _ _ hx
  | cpy => intro x hx; simp [mods] at hx; exact upd_ne _ _ hx
  | guess h => intro x hx; simp [mods] at hx; exact upd_ne _ _ hx
  | seq _ _ iha ihb =>
      intro x hx
      simp [mods, Finset.mem_union] at hx
      rw [ihb x (by simp [hx.2]), iha x (by simp [hx.1])]
  | iteT _ _ ih => intro x hx; simp [mods, Finset.mem_union] at hx; exact ih x (by simp [hx.1])
  | iteF _ _ ih => intro x hx; simp [mods, Finset.mem_union] at hx; exact ih x (by simp [hx.2])
  | chL _ ih => intro x hx; simp [mods, Finset.mem_union] at hx; exact ih x (by simp [hx.1])
  | chR _ ih => intro x hx; simp [mods, Finset.mem_union] at hx; exact ih x (by simp [hx.2])
  | whF => intro x _; rfl
  | whT _ _ _ ihb ihw =>
      intro x hx
      simp [mods] at hx
      rw [ihw x (by simpa [mods] using hx), ihb x (by simpa [mods] using hx)]

