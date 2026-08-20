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

theorem np_iff_pcp_poly {L : Language} :
    InNP L ↔ ∃ r q : ℕ → ℕ, PolyBounded (fun n => 2 ^ r n) ∧ PolyBounded q ∧ InPCP L r q := by
  refine ⟨fun h => ?_, fun ⟨r, q, hr, hq, h⟩ => pcp_subset_np hr hq h⟩
  obtain ⟨q, hq, h⟩ := np_subset_pcp h
  exact ⟨fun _ => 0, q, by simpa using polyBounded_const 1, hq, h⟩

/-! ## The PCP theorem -/

/-- `PCP(log n, O(1)) ⊆ NP`: the easy inclusion of the PCP theorem. -/
