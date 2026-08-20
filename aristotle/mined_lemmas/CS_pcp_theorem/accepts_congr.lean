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

theorem accepts_congr (Q : Query) (π π' : Nat → Bool) (h : ∀ i ∈ Q.pos, π i = π' i) :
    Q.accepts π = Q.accepts π' := by
  unfold Query.accepts
  rw [List.map_congr_left h]

/-! ### An abstract model of efficient computation -/

/-- An abstract model of efficient (think: polynomial-time) computability, with the two
closure properties used below.  Polynomial time satisfies these. -/
structure EffModel where
  /-- Efficiently computable binary predicates on words. -/
  Eff₂ : (Word → Word → Bool) → Prop
  /-- Efficiently computable ternary predicates on words. -/
  Eff₃ : (Word → Word → Word → Bool) → Prop
  /-- Efficiently computable maps from an input and a random string to a local test. -/
  EffQ : (Word → Word → Query) → Prop
  /-- Evaluating an efficiently produced local test against a proof written on a second
  tape is efficient. -/
  eff_eval : ∀ V : Word → Word → Query, EffQ V →
    Eff₃ (fun x w ρ => (V x ρ).accepts (fun i => w.getD i false))
  /-- A conjunction over all random strings of length `b n` is efficient as soon as
  `2 ^ b n` is polynomially bounded, i.e. `b n = O(log n)`. -/
  eff_forall : ∀ (g : Word → Word → Word → Bool) (b : Nat → Nat), Eff₃ g →
    PolyBounded (fun n => 2 ^ b n) →
    Eff₂ (fun x w => (allWords (b x.length)).all (fun ρ => g x w ρ))

/-- The two closure conditions are consistent: the model in which every function counts
as efficient satisfies them.  (This is only a non-vacuity check; the intended model is
polynomial time.) -/
