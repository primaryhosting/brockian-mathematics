/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

This file formalises the statement `NP = PCP(log n, 1)` — the PCP theorem — in a
concrete non-uniform (Boolean circuit) model of computation.  The development is
self-contained and uses no imports.

* `CS.Circuit` : Boolean circuits over an arbitrary type of input variables.
* `CS.NPVerifier` / `CS.NPpoly` : the class of languages possessing a
  polynomial-size verifier reading a polynomially long witness (the non-uniform
  version of `NP`).
* `CS.PCPVerifier` / `CS.PCPlogConst` : probabilistically checkable proof systems
  with logarithmic randomness (equivalently, polynomially many random strings),
  polynomially long proofs, perfect completeness, soundness error `1/2`, and a
  prescribed bound on the number of proof bits inspected.  `PCPlogConst` is the
  class `PCP(log n, O(1))`, where the query bound is a constant independent of
  the input length.

Proved here:

* `CS.pcp_subset_np` : `PCP(log n, q) ⊆ NP` for every query bound (the "easy"
  inclusion; it is proved by taking the conjunction of the verifier's decision
  circuits over all of the polynomially many random strings).
* `CS.np_subset_pcp_polyQueries` : every `NP` language has a PCP system with
  logarithmic randomness and *polynomially many* queries (so the model is not
  degenerate, and the whole content of the PCP theorem is the reduction of the
  number of queries to a constant).
* `CS.ppoly_subset_pcplogconst` : every language decidable by polynomial-size
  circuits lies in `PCP(log n, O(1))` (with zero queries), so the latter class
  is non-empty.
* `CS.pcp_theorem` : the PCP theorem, `NP = PCP(log n, O(1))`.  The hard
  inclusion `NP ⊆ PCP(log n, O(1))` (Arora–Safra, Arora–Lund–Motwani–Sudan–Szegedy)
  is *not* proved here; it enters as an explicit hypothesis `hard` of the
  theorem, while the easy inclusion is supplied by `CS.pcp_subset_np`.
-/

namespace CS

/-! ## Polynomially bounded functions -/

/-- `PolyBdd f` : the function `f : ℕ → ℕ` is bounded by a polynomial. -/

theorem ppoly_subset_pcplogconst {L : Language} (h : Ppoly L) : PCPlogConst L :=
  ⟨0, ppoly_subset_pcp_zeroQueries h⟩

/-! ## The PCP theorem -/

/--
**The PCP theorem**: `NP = PCP(log n, 1)`.

A language lies in `NP` if and only if it has a probabilistically checkable
proof system that uses `O(log n)` random bits and inspects only a constant
number of bits of the proof, with perfect completeness and soundness error
`1/2`.

The inclusion `PCP(log n, O(1)) ⊆ NP` is proved here (see `pcp_subset_np`): one
takes the conjunction of the decision circuits over all polynomially many random
strings.  The converse inclusion `NP ⊆ PCP(log n, O(1))` is the deep direction,
due to Arora–Safra and Arora–Lund–Motwani–Sudan–Szegedy; it is assumed here as
the explicit hypothesis `hard` rather than proved.
-/
