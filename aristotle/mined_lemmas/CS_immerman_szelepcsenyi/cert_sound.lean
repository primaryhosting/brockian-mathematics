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


theorem cert_sound {E : Fin m → Fin m → Bool} {s : Fin m} {i : ℕ} {e e' : Env}
    (hS : e vS = s.val) (hI : e vI = i) (h : Exec E cert e e') :
    reachB E s i (e vU) = true := by
  rw [cert] at h
  obtain ⟨a1, hc1, h⟩ := exec_seq_inv h
  obtain ⟨a2, hc2, h⟩ := exec_seq_inv h
  obtain ⟨a3, hloop, hfin⟩ := exec_seq_inv h
  rw [exec_cpy_inv hc1] at hc2
  rw [exec_zero_inv hc2] at hloop
  have key := wh_sound (E := E)
    (Inv := fun a => a vI = i ∧ a vS = s.val ∧ a vU = e vU ∧ a vJ ≤ i ∧
      reachB E s (a vJ) (a vW) = true) ?_ hloop ?_
  · obtain ⟨⟨hI3, hS3, hU3, hJ3, hR3⟩, _⟩ := key
    rcases exec_ite_inv hfin with ⟨hcc, hsk⟩ | ⟨_, hf⟩
    · have hwu : a3 vW = a3 vU := by simpa [evalCond] using hcc
      rw [exec_skip_inv hsk] at *
      rw [hwu, hU3] at hR3
      exact reachB_le hJ3 hR3
    · exact absurd hf (fun hh => exec_fail_inv hh)
  · rintro a a' ⟨hI1, hS1, hU1, hJ1, hR1⟩ hcond hbody
    have hlt : a vJ < a vI := by simpa [evalCond] using hcond
    rcases exec_ch_inv hbody with hL | hR
    · obtain ⟨b1, hg, hite⟩ := exec_seq_inv hL
      obtain ⟨k, hk, hb1⟩ := exec_guess_inv hg
      subst hb1
      rcases exec_ite_inv hite with ⟨hce, hbb⟩ | ⟨_, hf⟩
      · obtain ⟨b2, hcpy, hinc⟩ := exec_seq_inv hbb
        rw [exec_cpy_inv hcpy] at hinc
        obtain ⟨hlt2, hb2⟩ := exec_incr_inv hinc
        subst hb2
        have hedge : edgeB E (a vW) k = true := by
          simpa [evalCond] using hce
        refine ⟨by simp +decide [hI1], by simp +decide [hS1], by simp +decide [hU1],
          by simp +decide; omega, ?_⟩
        simp +decide
        exact reachB_step hR1 hedge
      · exact absurd hf (fun hh => exec_fail_inv hh)
    · rw [exec_cpy_inv hR]
      refine ⟨by simp +decide [hI1], by simp +decide [hS1], by simp +decide [hU1], ?_, ?_⟩
      · simp +decide [hI1]
      · simp +decide [hI1]
        exact reachB_le hJ1 hR1
  · refine ⟨by simp +decide [hI], by simp +decide [hS], by simp +decide, by simp +decide, ?_⟩
    simp +decide [hS]
    exact reachB_zero


/-- Completeness of the path-guessing loop. -/
