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


theorem flagBody_sound {E : Fin m → Fin m → Bool} {a a' : Env} (h : Exec E flagBody a a') :
    ((a' vF ≠ 0) ↔ (a vF ≠ 0 ∨ a vU = a vV ∨ edgeB E (a vU) (a vV) = true)) ∧
      ∀ x, x ≠ vF → a' x = a x := by
  have hframe : ∀ x, x ≠ vF → a' x = a x := by
    intro x hx
    refine exec_frame h x ?_
    revert hx
    revert x
    decide
  refine ⟨?_, hframe⟩
  rw [flagBody] at h
  obtain ⟨b1, h1, h2⟩ := exec_seq_inv h
  have key : ∀ (c : Cond) (b b2 : Env), Exec E (.ite c (setOne vF) .skip) b b2 →
      (evalCond E c b = true → b2 vF = 1) ∧ (evalCond E c b = false → b2 = b) := by
    intro c b b2 hb
    rcases exec_ite_inv hb with ⟨hc, hs⟩ | ⟨hc, hs⟩
    · refine ⟨fun _ => ?_, fun hcf => by rw [hc] at hcf; exact absurd hcf (by simp)⟩
      obtain ⟨b3, hz, hi⟩ := exec_seq_inv hs
      rw [exec_zero_inv hz] at hi
      obtain ⟨_, hb2⟩ := exec_incr_inv hi
      rw [hb2]
      simp
    · refine ⟨fun hct => by rw [hc] at hct; exact absurd hct (by simp), fun _ => ?_⟩
      exact exec_skip_inv hs
  obtain ⟨k1t, k1f⟩ := key _ _ _ h1
  obtain ⟨k2t, k2f⟩ := key _ _ _ h2
  have hb1U : b1 vU = a vU := by
    rcases Bool.eq_false_or_eq_true (evalCond E (.eqv vU vV) a) with hc | hc
    · exact exec_frame h1 vU (by decide)
    · rw [k1f hc]
  have hb1V : b1 vV = a vV := exec_frame h1 vV (by decide)
  constructor
  · intro hne
    rcases Bool.eq_false_or_eq_true (evalCond E (.eqv vU vV) a) with hc1 | hc1
    · exact Or.inr (Or.inl (by simpa [evalCond] using hc1))
    · rcases Bool.eq_false_or_eq_true (evalCond E (.edg vU vV) b1) with hc2 | hc2
      · have hc2' : edgeB E (a vU) (a vV) = true := by
          simp only [evalCond] at hc2
          rwa [hb1U, hb1V] at hc2
        exact Or.inr (Or.inr hc2')
      · rw [k2f hc2, k1f hc1] at hne
        exact Or.inl hne
  · intro hor
    rcases Bool.eq_false_or_eq_true (evalCond E (.edg vU vV) b1) with hc2 | hc2
    · rw [k2t hc2]
      simp
    · rcases Bool.eq_false_or_eq_true (evalCond E (.eqv vU vV) a) with hc1 | hc1
      · rw [k2f hc2, k1t hc1]
        simp
      · rw [k2f hc2, k1f hc1]
        rcases hor with h' | h' | h'
        · exact h'
        · exact absurd h' (by simpa [evalCond] using hc1)
        · have hc2' : edgeB E (a vU) (a vV) = false := by
            simp only [evalCond] at hc2
            rwa [hb1U, hb1V] at hc2
          rw [hc2'] at h'
          exact absurd h' (by simp)

