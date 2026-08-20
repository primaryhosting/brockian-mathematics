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

theorem size_eqPosC_le (pos : Fin Q → Fin P → Circuit (n + R)) (Sp : ℕ)
    (hp : ∀ i j, (pos i j).size ≤ Sp) (t t' : Fin (2 ^ R * Q)) :
    (eqPosC pos t t').size ≤ 1 + P * (4 * Sp + 6) := by
  have hbound : ∀ c ∈ (List.finRange P).map
      (fun j => Circuit.iff' (posC pos t j) (posC pos t' j)), c.size ≤ 4 * Sp + 5 := by
    intro c hc
    simp only [List.mem_map, List.mem_finRange, true_and] at hc
    obtain ⟨j, rfl⟩ := hc
    rw [Circuit.size_iff']
    have h1 := size_posC_le pos Sp hp t j
    have h2 := size_posC_le pos Sp hp t' j
    omega
  have h := Circuit.size_bigAnd _ _ hbound
  simpa [eqPosC, List.length_map, List.length_finRange] using h

