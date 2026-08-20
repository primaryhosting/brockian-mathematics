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


theorem immerman_szelepcsenyi {m : ℕ} (E : Fin m → Fin m → Bool) (s t : Fin m) :
    (∃ e, Exec E nonReach (initEnv s t) e) ↔
      ¬ Relation.ReflTransGen (fun a b => E a b = true) s t := by
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) s.isLt
  -- the state after the three initialisations
  set a3 : Env := upd (upd (upd (upd (initEnv s t) vZ 0) vC 0) vC
    ((upd (upd (initEnv s t) vZ 0) vC 0) vC + 1)) vI 0 with ha3
  have h3Z : a3 vZ = 0 := by simp +decide [ha3]
  have h3S : a3 vS = s.val := by simp +decide [ha3, initEnv]
  have h3T : a3 vTgt = t.val := by simp +decide [ha3, initEnv]
  have h3I : a3 vI = 0 := by simp +decide [ha3]
  have h3C : a3 vC = Rcard E s 0 := by simp +decide [ha3, Rcard_zero]
  constructor
  · rintro ⟨e', hrun⟩
    rw [nonReach] at hrun
    obtain ⟨b1, hb1, hrun⟩ := exec_seq_inv hrun
    obtain ⟨b2, hb2, hrun⟩ := exec_seq_inv hrun
    obtain ⟨b3, hb3, hrun⟩ := exec_seq_inv hrun
    obtain ⟨b4, hloop, hrun⟩ := exec_seq_inv hrun
    obtain ⟨b5, hcpy, hrun⟩ := exec_seq_inv hrun
    obtain ⟨b6, hchk, hfin⟩ := exec_seq_inv hrun
    -- identify `b3` with `a3`
    have hb3eq : b3 = a3 := by
      rw [exec_zero_inv hb1] at hb2
      obtain ⟨c, hz, hi⟩ := exec_seq_inv hb2
      rw [exec_zero_inv hz] at hi
      obtain ⟨_, hb2'⟩ := exec_incr_inv hi
      rw [hb2'] at hb3
      rw [exec_zero_inv hb3, ha3]
    subst hb3eq
    obtain ⟨h4I, h4C⟩ := layerLoop_sound h3Z h3S h3I h3C hloop
    have h4Z : b4 vZ = 0 := by rw [exec_frame hloop vZ (by decide), h3Z]
    have h4S : b4 vS = s.val := by rw [exec_frame hloop vS (by decide), h3S]
    have h4T : b4 vTgt = t.val := by rw [exec_frame hloop vTgt (by decide), h3T]
    rw [exec_cpy_inv hcpy] at hchk
    have hflag : (b6 vF ≠ 0) ↔ reachB E s (m+1) t.val = true :=
      checkV_sound (by simp +decide [h4I]) (by simp +decide [h4S]) (by simp +decide [h4T])
        (by simp +decide [h4C]) hchk
    have h6Z : b6 vZ = 0 := by
      rw [exec_frame hchk vZ (by decide)]
      simp +decide [h4Z]
    rcases exec_ite_inv hfin with ⟨hcc, _⟩ | ⟨_, hf⟩
    · have h6F : b6 vF = 0 := by
        have : b6 vF = b6 vZ := by simpa [evalCond] using hcc
        rw [this, h6Z]
      intro hrtg
      exact (hflag.2 (reachB_succ_iff_rtg.2 hrtg)) h6F
    · exact absurd hf (fun hh => exec_fail_inv hh)
  · intro hnr
    obtain ⟨b4, hloop⟩ := layerLoop_complete (E := E) (s := s) (m - a3 vI) a3 rfl
      (by omega) h3Z h3S (by rw [h3C, h3I])
    obtain ⟨h4I, h4C⟩ := layerLoop_sound h3Z h3S h3I h3C hloop
    have h4Z : b4 vZ = 0 := by rw [exec_frame hloop vZ (by decide), h3Z]
    have h4S : b4 vS = s.val := by rw [exec_frame hloop vS (by decide), h3S]
    have h4T : b4 vTgt = t.val := by rw [exec_frame hloop vTgt (by decide), h3T]
    obtain ⟨b6, hchk⟩ := checkV_complete (E := E) (s := s) (i := m)
      (e := upd b4 vV (b4 vTgt)) (by simp +decide [h4I]) (by simp +decide [h4S])
      (by simp +decide [h4C]) le_rfl
    have hflag : (b6 vF ≠ 0) ↔ reachB E s (m+1) t.val = true :=
      checkV_sound (by simp +decide [h4I]) (by simp +decide [h4S]) (by simp +decide [h4T])
        (by simp +decide [h4C]) hchk
    have h6Z : b6 vZ = 0 := by
      rw [exec_frame hchk vZ (by decide)]
      simp +decide [h4Z]
    have h6F : b6 vF = 0 := by
      by_contra hne
      exact hnr (reachB_succ_iff_rtg.1 (hflag.1 hne))
    refine ⟨b6, ?_⟩
    rw [nonReach]
    obtain ⟨d1, hd1, d2, hd2, hd3⟩ :
        ∃ d1, Exec E (.zero vZ) (initEnv s t) d1 ∧ ∃ d2, Exec E (setOne vC) d1 d2 ∧
          Exec E (.zero vI) d2 a3 :=
      ⟨_, Exec.zero, _, Exec.seq Exec.zero (Exec.incr (by simpa using hm)), Exec.zero⟩
    exact Exec.seq hd1 (Exec.seq hd2 (Exec.seq hd3 (Exec.seq hloop
      (Exec.seq Exec.cpy (Exec.seq hchk (Exec.iteT (by simp [evalCond, h6F, h6Z]) Exec.skip))))))


/-! ## Nondeterministic machines with an arbitrary finite configuration space -/

