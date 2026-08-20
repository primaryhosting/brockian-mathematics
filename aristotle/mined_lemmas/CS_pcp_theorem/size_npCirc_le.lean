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

lemma size_npCirc_le (V : PCPVerifier) {c k : ℕ}
    (hpos : ∀ n j b, (V.posCirc n j b).size ≤ c * (n + 1) ^ k) (n : ℕ) :
    (npCirc V n).size ≤ npSizeBound V c k n := by
  set B := 2 * (V.accCirc n).size + V.pbits n * (8 * (c * (n + 1) ^ k) + 6) + 12 with hB
  have hbound : ∀ d ∈ (((List.range (2 ^ V.rlen n)).map fun i => accCheckCirc V n i)
      ++ consList V n), d.size ≤ B := by
    intro d hd
    rw [List.mem_append] at hd
    rcases hd with hd | hd
    · rw [List.mem_map] at hd
      obtain ⟨i, _, rfl⟩ := hd
      have := size_accCheckCirc_le V n i
      omega
    · rw [consList, List.mem_flatMap] at hd
      obtain ⟨p, _, hd⟩ := hd
      rw [List.mem_map] at hd
      obtain ⟨p', _, rfl⟩ := hd
      have := size_consCheckCirc_le V hpos n p.1 p.2 p'.1 p'.2
      omega
  have hlen : (((List.range (2 ^ V.rlen n)).map fun i => accCheckCirc V n i)
      ++ consList V n).length
      = 2 ^ V.rlen n + (2 ^ V.rlen n * V.q) * (2 ^ V.rlen n * V.q) := by
    simp [consList, List.length_flatMap]
  have := Circ.size_bigAnd_le _ B hbound
  rw [hlen] at this
  simpa [npCirc, npSizeBound, hB] using this

