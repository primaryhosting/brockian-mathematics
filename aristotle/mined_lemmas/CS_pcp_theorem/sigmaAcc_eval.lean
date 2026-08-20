import Mathlib
import RequestProject.Circuits

/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option autoImplicit false

/-!
## Overview

This file formalises the statement `NP = PCP(log n, O(1))` (the PCP theorem) in the
non-uniform (Boolean circuit) model of efficient computation, and proves the "easy"
inclusion `PCP(log n, O(1)) ⊆ NP` in full.

*  A language is a predicate on bit strings (`CS.Language`).
*  `CS.InNP L` says that `L` has a polynomial-length witness that is checked by a
   polynomial-size Boolean circuit.
*  `CS.InPCP L` says that `L` has a probabilistically checkable proof system with
   `O(log n)` random bits, a constant number `q` of queries, perfect completeness and
   soundness error at most `1/2`; the query positions and the decision predicate are
   computed by polynomial-size circuits.

`CS.pcp_subset_np` proves `PCP(log n, O(1)) ⊆ NP` unconditionally: a witness for the NP
system is the table of answers of the PCP verifier on all `2^{O(log n)} = poly(n)` random
strings, together with the consistency requirement that two queries landing on the same
proof position receive the same answer.

Proof positions are named by bit strings of length `pbits n` with `pbits` polynomially
bounded; since the verifier only ever inspects `2 ^ rlen n * q = poly(n)` positions, no
further restriction on the proof length is needed.

The reverse inclusion `NP ⊆ PCP(log n, O(1))` is the deep content of the PCP theorem
(Arora–Safra, Arora–Lund–Motwani–Sudan–Szegedy); it is *not* proved here, and appears as
an explicit hypothesis `hard` of `CS.pcp_theorem`.
-/

namespace CS

/-- A language: a set of finite bit strings. -/
abbrev Language := List Bool → Prop

/-- The variable assignment described by a bit string (out-of-range variables are `false`). -/

lemma sigmaAcc_eval (V : PCPVerifier) (x w : List Bool) (i : ℕ)
    (hi : i < 2 ^ V.rlen x.length) :
    (fun t => (sigmaAcc V x.length i t).eval (asFun (x ++ w)))
      = asFun (x ++ rstr V x.length i ++ ansOf V w i) := by
  have hrlen : (rstr V x.length i).length = V.rlen x.length := length_rstr hi
  have hanslen : (ansOf V w i).length = V.q := by simp [ansOf]
  have hxr : (x ++ rstr V x.length i).length = x.length + V.rlen x.length := by
    rw [List.length_append, hrlen]
  funext t
  simp only [sigmaAcc]
  by_cases ht : t < x.length
  · rw [if_pos ht, Circ.eval_var, asFun_append_left x w ht,
      asFun_append_left _ (ansOf V w i) (by rw [hxr]; omega),
      asFun_append_left x _ ht]
  · rw [if_neg ht]
    by_cases ht2 : t < x.length + V.rlen x.length
    · rw [if_pos ht2, Circ.eval_cst,
        asFun_append_left _ (ansOf V w i) (by rw [hxr]; omega),
        asFun_append_right x _ (by omega), asFun_apply]
    · rw [if_neg ht2]
      by_cases ht3 : t < x.length + V.rlen x.length + V.q
      · have hj : t - x.length - V.rlen x.length < V.q := by omega
        rw [if_pos ht3, Circ.eval_var,
          show x.length + i * V.q + (t - x.length - V.rlen x.length)
              = x.length + (i * V.q + (t - x.length - V.rlen x.length)) by ring,
          asFun_append_add x w,
          asFun_append_right _ (ansOf V w i) (by rw [hxr]; omega), hxr, asFun_apply,
          show t - (x.length + V.rlen x.length) = t - x.length - V.rlen x.length by omega,
          ansOf, asFun_apply, getD_map_range _ hj]
      · rw [if_neg ht3, Circ.eval_cst]
        refine (asFun_of_length_le ?_).symm
        rw [List.length_append, hxr, hanslen]
        omega

