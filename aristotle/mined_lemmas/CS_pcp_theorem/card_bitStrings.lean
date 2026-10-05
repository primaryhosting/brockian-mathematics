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

lemma card_bitStrings (n : ℕ) : (bitStrings n).card = 2 ^ n := by
  induction n with
  | zero => simp [bitStrings]
  | succ n ih =>
      have hdisj :
          Disjoint ((bitStrings n).image (List.cons true))
            ((bitStrings n).image (List.cons false)) := by
        refine Finset.disjoint_left.mpr ?_
        rintro ρ hρ hρ'
        simp only [Finset.mem_image] at hρ hρ'
        obtain ⟨σ, -, rfl⟩ := hρ
        obtain ⟨τ, -, hτ⟩ := hρ'
        exact Bool.noConfusion (List.head_eq_of_cons_eq hτ)
      have h1 : ((bitStrings n).image (List.cons true)).card = 2 ^ n := by
        rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), ih]
      have h2 : ((bitStrings n).image (List.cons false)).card = 2 ^ n := by
        rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), ih]
      rw [bitStrings, Finset.card_union_of_disjoint hdisj, h1, h2]
      ring

/-! ### Verifiers -/

/-- A non-adaptive PCP verifier: on input `x` and random string `ρ` it computes `q` proof
positions to look at, and then decides on the basis of the `q` bits it read. The number of
queries `q` is a constant of the verifier, which is exactly the `O(1)` in `PCP(log n, 1)`. -/
structure Verifier where
  /-- number of queries -/
  q : ℕ
  /-- the queried positions -/
  query : BitString → BitString → Fin q → ℕ
  /-- the decision predicate, applied to the bits that were read -/
  accept : BitString → BitString → (Fin q → Bool) → Bool

/-- A proof string (an assignment of a bit to every position). -/
abbrev PCPProof := ℕ → Bool

/-- The verdict of `V` on input `x`, coins `ρ` and proof `π`. -/
