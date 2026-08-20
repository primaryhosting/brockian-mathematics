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

lemma npCirc_eval_iff (V : PCPVerifier) (x w : List Bool) :
    ((npCirc V x.length).eval (asFun (x ++ w)) = true) ↔
      ((∀ i < 2 ^ V.rlen x.length, V.accWith x (rstr V x.length i) (ansOf V w i) = true) ∧
        (∀ i < 2 ^ V.rlen x.length, ∀ j < V.q, ∀ i' < 2 ^ V.rlen x.length, ∀ j' < V.q,
          V.position x (rstr V x.length i) j = V.position x (rstr V x.length i') j' →
            w.getD (i * V.q + j) false = w.getD (i' * V.q + j') false)) := by
  rw [npCirc, Circ.eval_bigAnd]
  constructor
  · intro h
    constructor
    · intro i hi
      have hmem : accCheckCirc V x.length i ∈
          (((List.range (2 ^ V.rlen x.length)).map fun i => accCheckCirc V x.length i)
            ++ consList V x.length) := by
        apply List.mem_append_left
        exact List.mem_map_of_mem (by simpa using hi)
      have := h _ hmem
      rwa [accCheckCirc_eval V x w i hi] at this
    · intro i hi j hj i' hi' j' hj' hpos
      have hmem : consCheckCirc V x.length i j i' j' ∈
          (((List.range (2 ^ V.rlen x.length)).map fun i => accCheckCirc V x.length i)
            ++ consList V x.length) := by
        apply List.mem_append_right
        rw [consList, List.mem_flatMap]
        exact ⟨(i, j), mem_pairsList.2 ⟨hi, hj⟩,
          List.mem_map_of_mem (mem_pairsList.2 ⟨hi', hj'⟩)⟩
      have hc := h _ hmem
      rw [consCheckCirc, Circ.eval_impl] at hc
      have h1 : (posEqCirc V x.length i j i' j').eval (asFun (x ++ w)) = true :=
        (posEqCirc_eval V x w i j i' j').2 hpos
      have h2 := hc h1
      rw [Circ.eval_xnor, Circ.eval_var, Circ.eval_var,
        show x.length + i * V.q + j = x.length + (i * V.q + j) by ring,
        show x.length + i' * V.q + j' = x.length + (i' * V.q + j') by ring,
        asFun_append_add x w, asFun_append_add x w, asFun_apply, asFun_apply] at h2
      exact h2
  · rintro ⟨hacc, hcons⟩ c hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · rw [List.mem_map] at hc
      obtain ⟨i, hi, rfl⟩ := hc
      have hi' : i < 2 ^ V.rlen x.length := by simpa using hi
      rw [accCheckCirc_eval V x w i hi']
      exact hacc i hi'
    · rw [consList, List.mem_flatMap] at hc
      obtain ⟨p, hp, hc⟩ := hc
      rw [List.mem_map] at hc
      obtain ⟨p', hp', rfl⟩ := hc
      obtain ⟨hi, hj⟩ := mem_pairsList.1 (show (p.1, p.2) ∈ _ by simpa using hp)
      obtain ⟨hi', hj'⟩ := mem_pairsList.1 (show (p'.1, p'.2) ∈ _ by simpa using hp')
      rw [consCheckCirc, Circ.eval_impl]
      intro heq
      rw [Circ.eval_xnor]
      have hpos := (posEqCirc_eval V x w p.1 p.2 p'.1 p'.2).1 heq
      have hval := hcons p.1 hi p.2 hj p'.1 hi' p'.2 hj' hpos
      rw [Circ.eval_var, Circ.eval_var,
        show x.length + p.1 * V.q + p.2 = x.length + (p.1 * V.q + p.2) by ring,
        show x.length + p'.1 * V.q + p'.2 = x.length + (p'.1 * V.q + p'.2) by ring,
        asFun_append_add x w, asFun_append_add x w, asFun_apply, asFun_apply]
      exact hval

/-! ## Size bounds -/

/-- An explicit polynomial bound for the size of the simulating circuit. -/
