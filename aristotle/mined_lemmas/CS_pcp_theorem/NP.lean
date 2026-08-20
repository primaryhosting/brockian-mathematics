/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file develops, from first principles (no imports beyond the Lean core prelude),
a formal framework for probabilistically checkable proofs and states the PCP theorem
`NP = PCP(log n, 1)` inside it.

Design.

* Languages are predicates on binary words.
* "Efficient computability" is abstracted into a structure `CS.EffModel` carrying a
  predicate on functions (think: polynomial-time computable) together with two closure
  properties that polynomial time enjoys:
  - evaluating a (efficiently produced) local test against a candidate proof written on
    the witness tape is efficient;
  - a conjunction over all random strings of length `b n` is efficient whenever
    `2 ^ b n` is polynomially bounded (i.e. `b n = O(log n)`).
* A PCP verifier is given by an efficiently computable map sending an input `x` and a
  random string `ρ` to a *local test*: a list of at most `q` positions of the proof to
  read, together with the truth table of the predicate applied to the answers.
  Completeness is perfect and the soundness error is `1/2`, as in the standard
  definition of the class `PCP(r(n), q(n))`.

Results.

* `CS.pcp_subset_np`: unconditionally, `PCP(log n, O(1)) ⊆ NP` in any such model.
* `CS.pcp_theorem_iff`: unconditionally, the class equality `NP = PCP(log n, 1)` is
  equivalent to the inclusion `NP ⊆ PCP(log n, 1)`.
* `CS.pcp_theorem`: the class equality `NP = PCP(log n, 1)`, with the hard inclusion
  `NP ⊆ PCP(log n, 1)` (the Arora–Safra / Arora–Lund–Motwani–Sudan–Szegedy theorem,
  whose known proofs proceed by low-degree testing or by Dinur's gap amplification)
  taken as an explicit hypothesis. Everything else is proved here.
-/

namespace CS

/-- Binary words. -/
abbrev Word := List Bool

/-- A language is a set of binary words. -/
abbrev Language := Word → Prop

/-- `f` is bounded by a polynomial. -/

def NP (M : EffModel) (L : Language) : Prop :=
  ∃ (p : Nat → Nat) (R : Word → Word → Bool), PolyBounded p ∧ M.Eff₂ R ∧
    ∀ x, L x ↔ ∃ w : Word, w.length ≤ p x.length ∧ R x w = true

/-- `V` is a PCP verifier for `L` using `r n` random bits, at most `q` queries into a
proof of length `plen n`, with perfect completeness and soundness error `1/2`. -/
structure IsPCPVerifier (r : Nat → Nat) (q : Nat) (plen : Nat → Nat) (L : Language)
    (V : Word → Word → Query) : Prop where
  /-- At most `q` positions are queried. -/
  queries : ∀ x ρ, (V x ρ).pos.length ≤ q
  /-- All queried positions lie inside the proof. -/
  inRange : ∀ x ρ, ∀ i ∈ (V x ρ).pos, i < plen x.length
  /-- Perfect completeness: inputs in `L` have a proof accepted for every random string. -/
  completeness : ∀ x, L x → ∃ π : Nat → Bool, ∀ ρ ∈ allWords (r x.length),
    (V x ρ).accepts π = true
  /-- Soundness error `1/2`: for inputs outside `L`, no proof is accepted for more than
  half of the random strings. -/
  soundness : ∀ x, ¬ L x → ∀ π : Nat → Bool,
    2 * ((allWords (r x.length)).countP (fun ρ => (V x ρ).accepts π)) ≤
      (allWords (r x.length)).length

/-- The class `PCP(r(n), q)`: languages with a PCP verifier using `r n` random bits and
`q` queries, perfect completeness and soundness error `1/2`. -/
