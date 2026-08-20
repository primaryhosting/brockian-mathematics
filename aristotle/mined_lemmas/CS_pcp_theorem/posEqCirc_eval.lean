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

lemma posEqCirc_eval (V : PCPVerifier) (x w : List Bool) (i j i' j' : ℕ) :
    ((posEqCirc V x.length i j i' j').eval (asFun (x ++ w)) = true)
      ↔ V.position x (rstr V x.length i) j = V.position x (rstr V x.length i') j' := by
  rw [posEqCirc]
  rw [Circ.eval_bigAnd]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp,
    PCPVerifier.position]
  constructor
  · intro h
    refine List.map_inj_left.2 ?_
    intro b hb
    have hb' : b < V.pbits x.length := by simpa using hb
    have := h _ b hb' rfl
    rw [Circ.eval_xnor] at this
    rw [posBitCirc_eval, posBitCirc_eval] at this
    exact this
  · intro h c b hb hc
    subst hc
    rw [Circ.eval_xnor, posBitCirc_eval, posBitCirc_eval]
    have := List.map_inj_left.1 h b (by simpa using hb)
    exact this

