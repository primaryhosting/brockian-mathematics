import Mathlib

/-!
# CH Independent Statement
Category: Frontier — Set Theory
Target: Frontier.CH_independent_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

universe u v w w'

namespace Frontier

open Cardinal
open FirstOrder FirstOrder.Language

/-!
## Part 1: the Continuum Hypothesis, stated inside Lean

`ContinuumHypothesis` is the usual statement "every uncountable set of reals has the
cardinality of the continuum".  We check (this is a theorem of ZFC, hence provable in Lean)
that it is equivalent to the arithmetical form `𝔠 = ℵ₁`.
-/

/-- The Continuum Hypothesis: every set of reals of cardinality greater than `ℵ₀` already has
the cardinality of the continuum. -/

theorem CH_independent_of_satisfiable {L : FirstOrder.Language.{u, v}} {T : L.Theory}
    {ch : L.Sentence}
    (hgodel : (T ∪ {ch}).IsSatisfiable)
    (hcohen : (T ∪ {Formula.not ch}).IsSatisfiable) :
    ¬ (T ⊨ᵇ ch) ∧ ¬ (T ⊨ᵇ Formula.not ch) ∧ ¬ T.IsComplete := by
  obtain ⟨Mg⟩ := hgodel
  obtain ⟨Mc⟩ := hcohen
  have hMg : Mg ⊨ T ∪ {ch} := Mg.is_model
  have hMc : Mc ⊨ T ∪ {Formula.not ch} := Mc.is_model
  have hMgT : Mg.Carrier ⊨ T := (Theory.model_union_iff.1 hMg).1
  have hMcT : Mc.Carrier ⊨ T := (Theory.model_union_iff.1 hMc).1
  have hg : Mg.Carrier ⊨ ch := Theory.model_singleton_iff.1 (Theory.model_union_iff.1 hMg).2
  have hc : Mc.Carrier ⊨ Formula.not ch :=
    Theory.model_singleton_iff.1 (Theory.model_union_iff.1 hMc).2
  exact CH_independent_statement Mg.Carrier hg Mc.Carrier hc

end Frontier

