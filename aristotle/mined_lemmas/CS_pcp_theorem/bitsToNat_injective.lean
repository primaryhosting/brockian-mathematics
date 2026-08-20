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

theorem bitsToNat_injective : ∀ {m : ℕ}, Function.Injective (bitsToNat (m := m)) := by
  intro m
  induction m with
  | zero => intro f g _; funext j; exact absurd j.isLt (by omega)
  | succ m ih =>
      intro f g h
      simp only [bitsToNat] at h
      have h0 : f 0 = g 0 := by
        by_contra hne
        cases hf : f 0 <;> cases hg : g 0 <;> simp [hf, hg] at hne h <;> omega
      have htail : bitsToNat (fun j : Fin m => f j.succ) = bitsToNat (fun j : Fin m => g j.succ) := by
        rw [h0] at h
        cases hg : g 0 <;> simp [hg] at h <;> omega
      have := ih htail
      funext j
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · exact h0
      · exact congrFun this j'

/-! ## Languages, NP and PCP -/

/-- A language: for each input length, a predicate on bit strings of that length. -/
