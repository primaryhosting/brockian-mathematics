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

lemma size_consCheckCirc_le (V : PCPVerifier) {c k : ℕ}
    (hpos : ∀ n j b, (V.posCirc n j b).size ≤ c * (n + 1) ^ k) (n i j i' j' : ℕ) :
    (consCheckCirc V n i j i' j').size ≤ V.pbits n * (8 * (c * (n + 1) ^ k) + 6) + 12 := by
  set P := c * (n + 1) ^ k with hP
  have hxnor : ∀ d ∈ (List.range (V.pbits n)).map (fun b =>
      Circ.xnor (posBitCirc V n i j b) (posBitCirc V n i' j' b)), d.size ≤ 8 * P + 5 := by
    intro d hd
    rw [List.mem_map] at hd
    obtain ⟨b, _, rfl⟩ := hd
    rw [Circ.size_xnor]
    have h1 := size_posBitCirc_le V hpos n i j b
    have h2 := size_posBitCirc_le V hpos n i' j' b
    omega
  have hbig := Circ.size_bigAnd_le _ (8 * P + 5) hxnor
  rw [List.length_map, List.length_range] at hbig
  rw [consCheckCirc, Circ.size_impl, Circ.size_xnor]
  simp only [Circ.size]
  have : (posEqCirc V n i j i' j').size ≤ V.pbits n * (8 * P + 6) + 1 := by
    simpa [posEqCirc] using hbig
  omega

