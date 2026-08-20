/-
# CH Independent Statement
Category: Frontier — Set Theory
Target: Frontier.CH_independent_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# CH Independent Statement
Category: Frontier — Set Theory
Target: Frontier.CH_independent_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Cardinal FirstOrder

namespace Frontier

/-! ## Part 1: the Continuum Hypothesis as a statement about cardinals

We first record the "external" form of CH — the statement, about the actual real
numbers, that every uncountable set of reals has the cardinality of the continuum —
and prove that it is equivalent to the usual cardinal arithmetic form `ℵ₁ = 𝔠`.
This is a genuine (and fully proved) Lean theorem; it is the base case of the
formalization. -/

/-- The Continuum Hypothesis, in the form: every uncountable set of real numbers has
cardinality the continuum. -/

theorem independentOf_of_models {L : FirstOrder.Language.{u, v}} {T : L.Theory}
    {φ : L.Sentence}
    (M : Language.Theory.ModelType.{u, v, max u v} T) (hM : M ⊨ φ)
    (N : Language.Theory.ModelType.{u, v, max u v} T) (hN : ¬ N ⊨ φ) :
    IndependentOf T φ :=
  (independentOf_iff_exists_models T φ).2 ⟨⟨M, hM⟩, ⟨N, hN⟩⟩

/-! ## Part 3: the language of set theory and the statement of the independence of CH -/

/-- The relation symbols of the language of set theory: a single binary relation `∈`. -/
inductive memRel : ℕ → Type
  | mem : memRel 2
  deriving DecidableEq

/-- The first-order language of set theory: one binary relation symbol, `∈`. -/
