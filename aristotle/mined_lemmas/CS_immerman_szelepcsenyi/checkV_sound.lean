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


theorem checkV_sound {E : Fin m → Fin m → Bool} {s : Fin m} {i v : ℕ} {e e' : Env}
    (hI : e vI = i) (hS : e vS = s.val) (hV : e vV = v) (hC : e vC = Rcard E s i)
    (h : Exec E checkV e e') :
    (e' vF ≠ 0) ↔ reachB E s (i+1) v = true := by
  rw [checkV] at h
  obtain ⟨a1, hz1, h⟩ := exec_seq_inv h
  obtain ⟨a2, hz2, h⟩ := exec_seq_inv h
  obtain ⟨a3, hz3, h⟩ := exec_seq_inv h
  obtain ⟨a4, hloop, hfin⟩ := exec_seq_inv h
  rw [exec_zero_inv hz1] at hz2
  rw [exec_zero_inv hz2] at hz3
  rw [exec_zero_inv hz3] at hloop
  have key := wh_sound (E := E)
    (Inv := fun a => a vI = i ∧ a vS = s.val ∧ a vV = v ∧ a vC = e vC ∧ a vU ≤ m ∧
      a vCnt ≤ (Rlt E s i (a vU)).card ∧
      (a vF ≠ 0 → ∃ u, reachB E s i u = true ∧ (u = v ∨ edgeB E u v = true)) ∧
      (a vCnt = (Rlt E s i (a vU)).card → ∀ u, u < a vU → reachB E s i u = true →
        (u = v ∨ edgeB E u v = true) → a vF ≠ 0)) ?_ hloop ?_
  · obtain ⟨⟨hI4, hS4, hV4, hC4, hU4, hCnt4, hFa, hFb⟩, hcond⟩ := key
    have hUm : a4 vU = m := by
      have : ¬ (a4 vU < m) := by simpa [evalCond] using hcond
      omega
    rcases exec_ite_inv hfin with ⟨hcc, hsk⟩ | ⟨_, hf⟩
    · rw [exec_skip_inv hsk]
      have hcnt : a4 vCnt = a4 vC := by simpa [evalCond] using hcc
      rw [hC4, hC] at hcnt
      have hfull : a4 vCnt = (Rlt E s i (a4 vU)).card := by
        rw [hcnt, hUm]
        rfl
      rw [reachB_succ_iff']
      constructor
      · exact hFa
      · rintro ⟨u, hu, htest⟩
        exact hFb hfull u (by rw [hUm]; exact reachB_lt hu) hu htest
    · exact absurd hf (fun hh => exec_fail_inv hh)
  · -- the loop body preserves the invariant
    rintro a a' ⟨hI1, hS1, hV1, hC1, hU1, hCnt1, hFa1, hFb1⟩ hcond hbody
    have hUlt : a vU < m := by simpa [evalCond] using hcond
    rw [countBody] at hbody
    obtain ⟨b, hb, hinc⟩ := exec_seq_inv hbody
    obtain ⟨hbUlt, ha'⟩ := exec_incr_inv hinc
    rcases exec_ch_inv hb with hL | hR
    · -- the vertex `a vU` is certified
      obtain ⟨c1, hcert, hrest⟩ := exec_seq_inv hL
      obtain ⟨c2, hcnt, hflag⟩ := exec_seq_inv hrest
      have hreach : reachB E s i (a vU) = true := cert_sound hS1 hI1 hcert
      have hc1 : ∀ x, x ∉ ({vW, vJ, vT} : Finset Var) → c1 x = a x := by
        intro x hx
        refine exec_frame hcert x ?_
        revert hx
        revert x
        decide
      obtain ⟨hltc, hc2eq⟩ := exec_incr_inv hcnt
      obtain ⟨hflagiff, hflagframe⟩ := flagBody_sound hflag
      have hc2 : ∀ x, x ≠ vCnt → c2 x = c1 x := by
        intro x hx
        rw [hc2eq]
        exact upd_ne _ _ hx
      have hbU : b vU = a vU := by
        rw [hflagframe vU (by decide), hc2 vU (by decide), hc1 vU (by decide)]
      have hbV : b vV = v := by
        rw [hflagframe vV (by decide), hc2 vV (by decide), hc1 vV (by decide), hV1]
      have hbI : b vI = i := by
        rw [hflagframe vI (by decide), hc2 vI (by decide), hc1 vI (by decide), hI1]
      have hbS : b vS = s.val := by
        rw [hflagframe vS (by decide), hc2 vS (by decide), hc1 vS (by decide), hS1]
      have hbC : b vC = e vC := by
        rw [hflagframe vC (by decide), hc2 vC (by decide), hc1 vC (by decide), hC1]
      have hbCnt : b vCnt = a vCnt + 1 := by
        rw [hflagframe vCnt (by decide), hc2eq]
        simp [hc1 vCnt (by decide)]
      have hc2U : c2 vU = a vU := by rw [hc2 vU (by decide), hc1 vU (by decide)]
      have hc2V : c2 vV = v := by rw [hc2 vV (by decide), hc1 vV (by decide), hV1]
      have hc2F : c2 vF = a vF := by rw [hc2 vF (by decide), hc1 vF (by decide)]
      have hcardsucc : (Rlt E s i (a vU + 1)).card = (Rlt E s i (a vU)).card + 1 :=
        Rlt_card_succ_pos hreach
      subst ha'
      refine ⟨by simp +decide [hbI], by simp +decide [hbS], by simp +decide [hbV],
        by simp +decide [hbC], by simp +decide [hbU]; omega, ?_, ?_, ?_⟩
      · simp +decide [hbCnt, hbU, hcardsucc]
        omega
      · intro hne
        simp +decide at hne
        rcases hflagiff.1 hne with h' | h' | h'
        · exact hFa1 (by rwa [hc2F] at h')
        · exact ⟨a vU, hreach, Or.inl (by rw [← hc2U, ← hc2V]; exact h')⟩
        · exact ⟨a vU, hreach, Or.inr (by rw [← hc2U, ← hc2V]; exact h')⟩
      · intro heq u hu hru htest
        simp +decide [hbCnt, hbU, hcardsucc] at heq
        have heq' : a vCnt = (Rlt E s i (a vU)).card := by omega
        simp +decide
        rcases Nat.lt_or_ge u (a vU) with hlt | hge
        · refine hflagiff.2 (Or.inl ?_)
          rw [hc2F]
          exact hFb1 heq' u hlt hru htest
        · have : u = a vU := by
            have : u < a vU + 1 := by simpa [hbU] using hu
            omega
          subst this
          rcases htest with h' | h'
          · exact hflagiff.2 (Or.inr (Or.inl (by rw [hc2U, hc2V]; exact h')))
          · exact hflagiff.2 (Or.inr (Or.inr (by rw [hc2U, hc2V]; exact h')))
    · -- the vertex `a vU` is skipped
      have hba : a = b := (exec_skip_inv hR).symm
      subst hba
      subst ha'
      refine ⟨by simp +decide [hI1], by simp +decide [hS1], by simp +decide [hV1],
        by simp +decide [hC1], by simp +decide; omega, ?_, ?_, ?_⟩
      · simp +decide
        exact le_trans hCnt1 Rlt_card_mono
      · intro hne
        simp +decide at hne
        exact hFa1 hne
      · intro heq u hu hru htest
        simp +decide at heq hu ⊢
        have hmono := Rlt_card_mono (E := E) (s := s) (i := i) (k := a vU)
        have hnr : ¬ reachB E s i (a vU) = true := by
          intro hr
          rw [Rlt_card_succ_pos hr] at heq
          omega
        have heq' : a vCnt = (Rlt E s i (a vU)).card := by
          rw [Rlt_card_succ_neg hnr] at heq
          exact heq
        have hlt : u < a vU := by
          rcases Nat.lt_or_ge u (a vU) with h' | h'
          · exact h'
          · have : u = a vU := by omega
            subst this
            exact absurd hru hnr
        exact hFb1 heq' u hlt hru htest
  · -- the invariant holds initially
    refine ⟨by simp +decide [hI], by simp +decide [hS], by simp +decide [hV],
      by simp +decide, by simp +decide, ?_, ?_, ?_⟩
    · simp +decide [Rlt]
    · simp +decide
    · intro _ u hu
      simp +decide at hu

