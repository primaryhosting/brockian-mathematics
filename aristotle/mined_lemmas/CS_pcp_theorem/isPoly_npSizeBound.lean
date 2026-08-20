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

lemma isPoly_npSizeBound (V : PCPVerifier) (c k : ℕ) : IsPoly (npSizeBound V c k) := by
  have hR : IsPoly fun n => 2 ^ V.rlen n := V.rand_log
  have hq : IsPoly fun _ : ℕ => V.q := isPoly_const _
  have hA : IsPoly fun n => (V.accCirc n).size := V.acc_size_poly
  have hP : IsPoly fun n => V.pbits n := V.pbits_poly
  have hc : IsPoly fun n => c * (n + 1) ^ k := ⟨c, k, fun _ => le_refl _⟩
  have h1 : IsPoly fun n => 2 ^ V.rlen n * V.q := hR.mul hq
  have h2 : IsPoly fun n => (2 ^ V.rlen n * V.q) * (2 ^ V.rlen n * V.q) := h1.mul h1
  have h3 : IsPoly fun n => 2 ^ V.rlen n + (2 ^ V.rlen n * V.q) * (2 ^ V.rlen n * V.q) :=
    hR.add h2
  have h4 : IsPoly fun n => 2 * (V.accCirc n).size := (isPoly_const 2).mul hA
  have h5 : IsPoly fun n => V.pbits n * (8 * (c * (n + 1) ^ k) + 6) :=
    hP.mul (((isPoly_const 8).mul hc).add (isPoly_const 6))
  have h6 : IsPoly fun n =>
      (2 * (V.accCirc n).size + V.pbits n * (8 * (c * (n + 1) ^ k) + 6) + 12) + 1 :=
    ((h4.add h5).add (isPoly_const 12)).add (isPoly_const 1)
  exact (h3.mul h6).add (isPoly_const 1)

/-! ## The easy inclusion: PCP(log n, O(1)) ⊆ NP -/

/-- The proof function reconstructed from a consistent answer table. -/
