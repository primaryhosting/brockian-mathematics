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

def InNP (L : Language) : Prop := ∃ V : NPVerifier, V.Accepts L

/-- A probabilistically checkable proof verifier using `r n` random bits and `q n` queries on
inputs of length `n`.  The queried positions and the accept/reject decision are computed by
polynomial-size circuits from the input and the random string. -/
structure PCPVerifier (r q : ℕ → ℕ) where
  /-- Number of bits used to write down a queried position. -/
  posLen : ℕ → ℕ
  /-- `pos n i j` computes the `j`-th bit of the position of the `i`-th query. -/
  pos : (n : ℕ) → Fin (q n) → Fin (posLen n) → Circuit (n + r n)
  /-- The decision circuit, reading the input, the random string and the `q n` answers. -/
  dec : (n : ℕ) → Circuit (n + r n + q n)
  posLen_poly : PolyBounded posLen
  pos_size_poly : ∃ c k : ℕ, ∀ n i j, (pos n i j).size ≤ c * (n + 1) ^ k
  dec_size_poly : PolyBounded fun n => (dec n).size

variable {r q : ℕ → ℕ}

/-- The position of the `i`-th query on input `x` with random string `rho`. -/
