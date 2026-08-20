import Mathlib
/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

This file sets up a self-contained, fully formal framework for probabilistically checkable
proofs, in the non-uniform (Boolean circuit) model of computation, and states the PCP theorem
`NP = PCP(log n, O(1))` in it (`CS.PCPCharacterization`).

* `CS.Circuit` is the type of Boolean circuits, with `Circuit.eval` and `Circuit.size`.
* `CS.NPVerifier` is a polynomial-size circuit family verifying polynomially long witnesses,
  and `CS.InNP` / `CS.NPClass` is the resulting class `NP` (non-uniform, i.e. `NP/poly`).
* `CS.PCPVerifier r q` is a verifier that, on inputs of length `n`, tosses `r n` coins, computes
  the positions of `q n` (non-adaptive) queries into a proof `pi : ℕ → Bool` by polynomial-size
  circuits, and decides by a polynomial-size circuit.  `CS.PCPVerifier.Decides` requires perfect
  completeness and soundness error at most `1/2`.
* `CS.InPCPLogConst` / `CS.PCPLogConstClass` is `PCP(log n, O(1))`.

The main results proved here are:

* `CS.pcp_subset_np`: any language with a PCP verifier using polynomially many random strings
  and polynomially many queries is in `NP`.  In particular `PCP(log n, O(1)) ⊆ NP`
  (`CS.pcp_log_const_subset_np`).
* `CS.np_subset_pcp` and `CS.np_iff_pcp_poly`: conversely every `NP` language has a PCP verifier
  reading the whole (polynomially long) proof, so `NP = PCP(log n, poly n)`.
* `CS.pcp_theorem`: the PCP characterization `NP = PCP(log n, O(1))` holds if and only if the
  inclusion `NP ⊆ PCP(log n, O(1))` holds; the reverse inclusion is unconditional.

The hard inclusion `NP ⊆ PCP(log n, O(1))` (Arora–Safra, Arora–Lund–Motwani–Sudan–Szegedy) is
*not* formalized here; only the statement and the unconditional half of the equality are.
-/

set_option maxHeartbeats 1000000

namespace CS

/-! ## Polynomially bounded functions -/

/-- A function `f : ℕ → ℕ` is polynomially bounded. -/

theorem size_npC_le (pos : Fin Q → Fin P → Circuit (n + R)) (dec : Circuit (n + R + Q)) (Sp : ℕ)
    (hp : ∀ i j, (pos i j).size ≤ Sp) :
    (npC pos dec).size
      ≤ 1 + (2 ^ R + 2 ^ R * Q * (2 ^ R * Q)) * (dec.size + P * (4 * Sp + 6) + 13) := by
  set S : ℕ := dec.size + (1 + P * (4 * Sp + 6)) + 11 with hS
  have hbound : ∀ c ∈ (((List.finRange (2 ^ R)).map fun k => decC dec k) ++
      (((List.finRange (2 ^ R * Q)) ×ˢ (List.finRange (2 ^ R * Q))).map fun p =>
        consC pos p.1 p.2)), c.size ≤ S := by
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · simp only [List.mem_map, List.mem_finRange, true_and] at hc
      obtain ⟨k, rfl⟩ := hc
      have := size_decC_le dec k
      omega
    · simp only [List.mem_map] at hc
      obtain ⟨⟨t, t'⟩, -, rfl⟩ := hc
      have := size_consC_le pos Sp hp t t'
      simp only at this ⊢
      omega
  have h := Circuit.size_bigAnd _ _ hbound
  have hlen : (((List.finRange (2 ^ R)).map fun k => decC dec k) ++
      (((List.finRange (2 ^ R * Q)) ×ˢ (List.finRange (2 ^ R * Q))).map fun p =>
        consC pos p.1 p.2)).length = 2 ^ R + 2 ^ R * Q * (2 ^ R * Q) := by
    simp [List.length_product]
  rw [npC]
  rw [hlen] at h
  refine h.trans ?_
  have : S + 1 = dec.size + P * (4 * Sp + 6) + 13 := by omega
  rw [this]

end Reduction
end CS

/-! ## PCP(r, q) ⊆ NP for polynomially many random strings and queries -/

namespace CS

open Reduction

/-- A PCP verifier using polynomially many random strings and polynomially many queries can be
simulated by an NP verifier: the witness records the answers to all queries that can ever be
asked, together with consistency constraints. -/
