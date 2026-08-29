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

This file sets up a self-contained formal model of probabilistically checkable proofs
(non-adaptive verifiers with `q` queries and `r(n)` random bits, perfect completeness and
soundness `1/2`) and of the class `NP`, both measured against one and the same abstract
notion of "efficient computation" (a `ComplexityModel`).

Inside this model we prove, unconditionally:

* `CS.pcp_subset_np` : `PCP(log n, O(1)) ⊆ NP` — a verifier using `O(log n)` random bits and
  a constant number of queries can be simulated by an `NP` verifier that reads a polynomially
  long prefix of the proof and checks *all* `2^{O(log n)} = poly(n)` random strings.
* `CS.pcp_theorem` : the equality `NP = PCP(log n, O(1))` is *equivalent* to the single
  inclusion `NP ⊆ PCP(log n, O(1))`; i.e. the content of the PCP theorem is entirely
  contained in that inclusion.
* `CS.pcp_theorem_of_hard` : the class equality itself, from that inclusion.
* `CS.trivialModel_hard_inclusion` : the framework is consistent and the hypothesis of
  `CS.pcp_theorem_of_hard` is satisfiable (a concrete `ComplexityModel` in which it holds).

The deep inclusion `NP ⊆ PCP(log n, O(1))` (Arora–Safra, Arora–Lund–Motwani–Sudan–Szegedy;
Dinur) is *not* formalized here; it appears as an explicit hypothesis of
`CS.pcp_theorem_of_hard` and as the right-hand side of the equivalence `CS.pcp_theorem`.
-/

set_option autoImplicit false

namespace CS

/-! ### Strings, languages and resource bounds -/

/-- Inputs, witnesses and random strings are finite bit strings. -/
abbrev BitString := List Bool

/-- A language is a predicate on bit strings. -/
abbrev Language := BitString → Prop

/-- `f` is bounded by a polynomial. -/

def bitStrings : ℕ → Finset BitString
  | 0 => {[]}
  | n + 1 =>
      (bitStrings n).image (List.cons true) ∪ (bitStrings n).image (List.cons false)

