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


theorem stepPhase_sound {E : Fin m → Fin m → Bool} {s : Fin m} {i : ℕ} {e e' : Env}
    (hI : e vI = i) (hS : e vS = s.val) (hC : e vC = Rcard E s i) (hZ : e vZ = 0)
    (h : Exec E stepPhase e e') : e' vC2 = Rcard E s (i+1) := by
  rw [stepPhase] at h
  obtain ⟨a1, hz1, h⟩ := exec_seq_inv h
  obtain ⟨a2, hz2, hloop⟩ := exec_seq_inv h
  rw [exec_zero_inv hz1] at hz2
  rw [exec_zero_inv hz2] at hloop
  have key := wh_sound (E := E)
    (Inv := fun a => a vI = i ∧ a vS = s.val ∧ a vC = Rcard E s i ∧ a vZ = 0 ∧ a vV ≤ m ∧
      a vC2 = (Rlt E s (i+1) (a vV)).card) ?_ hloop ?_
  · obtain ⟨⟨_, _, _, _, hVm, hC2⟩, hcond⟩ := key
    have hVm' : e' vV = m := by
      have : ¬ (e' vV < m) := by simpa [evalCond] using hcond
      omega
    rw [hC2, hVm']
    rfl
  · rintro a a' ⟨hI1, hS1, hC1, hZ1, hV1, hC21⟩ hcond hbody
    have hVlt : a vV < m := by simpa [evalCond] using hcond
    rw [vertexBody] at hbody
    obtain ⟨b, hchk, hrest⟩ := exec_seq_inv hbody
    obtain ⟨c, hite, hinc⟩ := exec_seq_inv hrest
    have hbI : b vI = i := by rw [exec_frame hchk vI (by decide), hI1]
    have hbS : b vS = s.val := by rw [exec_frame hchk vS (by decide), hS1]
    have hbV : b vV = a vV := exec_frame hchk vV (by decide)
    have hbC : b vC = Rcard E s i := by rw [exec_frame hchk vC (by decide), hC1]
    have hbZ : b vZ = 0 := by rw [exec_frame hchk vZ (by decide), hZ1]
    have hbC2 : b vC2 = (Rlt E s (i+1) (a vV)).card := by
      rw [exec_frame hchk vC2 (by decide), hC21]
    have hflag : (b vF ≠ 0) ↔ reachB E s (i+1) (a vV) = true :=
      checkV_sound hI1 hS1 rfl hC1 hchk
    obtain ⟨hltv, hc'⟩ := exec_incr_inv hinc
    have hcC2 : c vC2 = (Rlt E s (i+1) (a vV + 1)).card ∧ c vV = a vV ∧ c vI = i ∧
        c vS = s.val ∧ c vC = Rcard E s i ∧ c vZ = 0 := by
      rcases exec_ite_inv hite with ⟨hcc, hsk⟩ | ⟨hcc, hin⟩
      · -- flag is zero: the vertex is not in the next layer
        have hb0 : b vF = 0 := by
          have : b vF = b vZ := by simpa [evalCond] using hcc
          rw [this, hbZ]
        have hnr : ¬ reachB E s (i+1) (a vV) = true := by
          intro hr
          exact absurd hb0 (hflag.2 hr)
        rw [exec_skip_inv hsk]
        refine ⟨?_, hbV, hbI, hbS, hbC, hbZ⟩
        rw [hbC2, Rlt_card_succ_neg hnr]
      · have hb0 : b vF ≠ 0 := by
          intro h0
          have : ¬ (b vF = b vZ) := by simpa [evalCond] using hcc
          exact this (by rw [h0, hbZ])
        have hr : reachB E s (i+1) (a vV) = true := hflag.1 hb0
        obtain ⟨_, hc⟩ := exec_incr_inv hin
        rw [hc]
        refine ⟨?_, by simp +decide [hbV], by simp +decide [hbI], by simp +decide [hbS],
          by simp +decide [hbC], by simp +decide [hbZ]⟩
        simp +decide [hbC2, Rlt_card_succ_pos hr]
    obtain ⟨hcC2', hcV, hcI, hcS, hcC, hcZ⟩ := hcC2
    rw [hc']
    refine ⟨by simp +decide [hcI], by simp +decide [hcS], by simp +decide [hcC],
      by simp +decide [hcZ], by simp +decide [hcV]; omega, ?_⟩
    simp +decide [hcV, hcC2']
  · refine ⟨by simp +decide [hI], by simp +decide [hS], by simp +decide [hC],
      by simp +decide [hZ], by simp +decide, by simp +decide [Rlt]⟩

/-- Completeness of the vertex loop of the layer-counting phase. -/
