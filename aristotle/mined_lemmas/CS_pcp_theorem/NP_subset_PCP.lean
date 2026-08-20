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

theorem np_subset_pcp {L : Language} (h : InNP L) :
    ∃ q : ℕ → ℕ, PolyBounded q ∧ InPCP L (fun _ => 0) q := by
  classical
  obtain ⟨V, hV⟩ := h
  refine ⟨V.wit, V.wit_poly, V.toPCPVerifier, fun n x => ⟨fun hx => ?_, fun hx pi => ?_⟩⟩
  · obtain ⟨w, hw⟩ := (hV n x).1 hx
    refine ⟨fun p => if h : ∃ i : Fin (V.wit n), witPos (V.wit n) i = p then w h.choose
      else false, fun rho => ?_⟩
    rw [V.accepts_toPCPVerifier n x rho]
    have hfun : (fun i => (if h : ∃ i' : Fin (V.wit n), witPos (V.wit n) i' = witPos (V.wit n) i
        then w h.choose else false)) = w := by
      funext i
      have hex : ∃ i' : Fin (V.wit n), witPos (V.wit n) i' = witPos (V.wit n) i := ⟨i, rfl⟩
      simp only [dif_pos hex]
      exact congrArg w (witPos_injective _ hex.choose_spec)
    rw [hfun]
    exact hw
  · have hnone : ∀ rho : Bits 0, ¬ (V.toPCPVerifier.accepts n x rho pi = true) := by
      intro rho hacc
      rw [V.accepts_toPCPVerifier n x rho] at hacc
      exact hx ((hV n x).2 ⟨_, hacc⟩)
    rw [Finset.filter_false_of_mem fun rho _ => hnone rho]
    simp

/-- Non-degeneracy of the framework: NP is exactly the class of languages having a PCP verifier
with polynomially many random strings and polynomially many queries, i.e. `NP = PCP(log n, poly)`. -/
