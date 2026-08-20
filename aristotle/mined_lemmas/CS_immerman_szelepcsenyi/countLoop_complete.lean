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


theorem countLoop_complete {E : Fin m → Fin m → Bool} {s : Fin m} {i : ℕ} (hi : i ≤ m) :
    ∀ (d : ℕ) (a : Env), m - a vU = d → a vU ≤ m → a vI = i → a vS = s.val →
      a vCnt = (Rlt E s i (a vU)).card →
      ∃ a', Exec E countLoop a a' ∧ a' vU = m ∧ a' vCnt = (Rlt E s i m).card := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro a hd hUm hI hS hCnt
    rcases Nat.lt_or_ge (a vU) m with hlt | hge
    · -- one more iteration
      have hbody : ∃ a', Exec E countBody a a' ∧ a' vU = a vU + 1 ∧
          a' vCnt = (Rlt E s i (a vU + 1)).card := by
        by_cases hr : reachB E s i (a vU) = true
        · obtain ⟨c1, hcert⟩ := cert_complete hS hI hi hr
          have hc1 : ∀ x, x ∉ ({vW, vJ, vT} : Finset Var) → c1 x = a x := by
            intro x hx
            refine exec_frame hcert x ?_
            revert hx; revert x; decide
          have hc1Cnt : c1 vCnt = a vCnt := hc1 vCnt (by decide)
          have hcltm : c1 vCnt < m := by
            rw [hc1Cnt, hCnt]
            exact lt_of_le_of_lt Rlt_card_le hlt
          obtain ⟨b, hfb⟩ := flagBody_complete (lt_of_le_of_lt (Nat.zero_le _) hlt)
            (upd c1 vCnt (c1 vCnt + 1))
          obtain ⟨_, hframe⟩ := flagBody_sound hfb
          have hbU : b vU = a vU := by
            rw [hframe vU (by decide), upd_ne _ _ (by decide), hc1 vU (by decide)]
          have hbCnt : b vCnt = a vCnt + 1 := by
            rw [hframe vCnt (by decide)]
            simp [hc1Cnt]
          refine ⟨upd b vU (b vU + 1), Exec.seq (Exec.chL (Exec.seq hcert
            (Exec.seq (Exec.incr hcltm) hfb))) (Exec.incr (by rw [hbU]; exact hlt)), ?_, ?_⟩
          · simp [hbU]
          · rw [upd_ne _ _ (by decide), hbCnt, hCnt, Rlt_card_succ_pos hr]
        · refine ⟨upd a vU (a vU + 1),
            Exec.seq (Exec.chR Exec.skip) (Exec.incr hlt), by simp, ?_⟩
          rw [upd_ne _ _ (by decide), hCnt, Rlt_card_succ_neg hr]
      obtain ⟨a1, hrun1, hU1, hCnt1⟩ := hbody
      have hI1 : a1 vI = i := by rw [exec_frame hrun1 vI (by decide), hI]
      have hS1 : a1 vS = s.val := by rw [exec_frame hrun1 vS (by decide), hS]
      obtain ⟨a', hrun', hU', hCnt'⟩ := ih (m - a1 vU) (by omega) a1 rfl (by omega) hI1 hS1
        (by rw [hCnt1, hU1])
      exact ⟨a', Exec.whT (by simp [evalCond, hlt]) hrun1 hrun', hU', hCnt'⟩
    · have hUm' : a vU = m := by omega
      refine ⟨a, Exec.whF (by simp [evalCond]; omega), hUm', ?_⟩
      rw [hCnt, hUm']

