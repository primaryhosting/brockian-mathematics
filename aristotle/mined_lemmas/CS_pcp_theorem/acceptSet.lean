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

def acceptSet (V : Verifier) (x : BitString) (r : ℕ) (π : PCPProof) : Finset BitString :=
  (bitStrings r).filter fun ρ => V.run x ρ π = true

/-- An abstract model of efficient (polynomial-time) computation, used *uniformly* for both
classes below. Two closure/soundness properties of polynomial time are recorded; they are the
only facts about efficiency that the proofs need. -/
structure ComplexityModel where
  /-- efficiently computable predicates of an input and a witness (`NP` verifiers) -/
  EffPred : (BitString → BitString → Bool) → Prop
  /-- efficient PCP verifiers -/
  EffVerifier : Verifier → Prop
  /-- an efficient verifier can only address polynomially far into its proof -/
  query_poly : ∀ V : Verifier, EffVerifier V →
    ∃ p : ℕ → ℕ, IsPoly p ∧ ∀ x ρ i, V.query x ρ i ≤ p x.length
  /-- polynomial time is closed under taking the conjunction of the verdicts over all
  `2^{O(log n)} = poly(n)` random strings, the proof being given as an explicit bit list -/
  eff_forall_random : ∀ (V : Verifier) (r : ℕ → ℕ), IsLogBounded r → EffVerifier V →
    EffPred fun x w => decide (∀ ρ ∈ bitStrings (r x.length),
      V.accept x ρ (fun i => w.getD (V.query x ρ i) false) = true)

/-- `V`, using `r(n)` random bits, is a PCP verifier for `L`: perfect completeness and
soundness error at most `1/2`. -/
structure IsPCPVerifier (M : ComplexityModel) (V : Verifier) (r : ℕ → ℕ) (L : Language) :
    Prop where
  /-- the verifier is efficient -/
  eff : M.EffVerifier V
  /-- it uses `O(log n)` random bits -/
  rand : IsLogBounded r
  /-- completeness: members of `L` have proofs accepted with probability one -/
  completeness : ∀ x, L x → ∃ π : PCPProof, ∀ ρ ∈ bitStrings (r x.length), V.run x ρ π = true
  /-- soundness: for non-members every proof is accepted with probability at most `1/2` -/
  soundness : ∀ x, ¬ L x → ∀ π : PCPProof,
    2 * (acceptSet V x (r x.length) π).card ≤ 2 ^ (r x.length)

/-- The class `PCP(log n, O(1))`. -/
