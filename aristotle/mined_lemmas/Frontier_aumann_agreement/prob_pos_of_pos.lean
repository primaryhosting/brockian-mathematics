import Mathlib

/-!
# Aumann Agreement
Category: Frontier Mind
Target: Frontier.aumann_agreement
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

variable {Ω : Type*} [DecidableEq Ω]

/-- The probability of the (finite) event `S` under the weight function `p`. -/

lemma prob_pos_of_pos {p : Ω → ℝ} (hp : ∀ ω, 0 < p ω) {S : Finset Ω} (hS : S.Nonempty) :
    0 < prob p S :=
  Finset.sum_pos (fun ω _ => hp ω) hS

/-- An *information partition* of the state space: `I ω` is the set of states that the agent
cannot distinguish from `ω`.  The two axioms say that the cells `I ω` form a partition of `Ω`. -/
structure IsPartition (I : Ω → Finset Ω) : Prop where
  /-- Every state belongs to its own information cell. -/
  mem_self : ∀ ω, ω ∈ I ω
  /-- Two cells that meet are equal. -/
  eq_of_mem : ∀ ω ω' : Ω, ω' ∈ I ω → I ω' = I ω

/-- An event `M` is *common knowledge at `ω₀`* for the two agents with information partitions
`I₁`, `I₂` when `ω₀ ∈ M` and `M` is self-evident to both agents, i.e. `M` is a union of cells
of `I₁` and also a union of cells of `I₂`.  (Equivalently, `M` is a cell of the meet of the two
partitions containing `ω₀`.) -/
structure IsCommonKnowledgeAt (I₁ I₂ : Ω → Finset Ω) (M : Finset Ω) (ω₀ : Ω) : Prop where
  /-- The current state lies in `M`. -/
  mem : ω₀ ∈ M
  /-- `M` is a union of cells of agent 1. -/
  closed₁ : ∀ ω ∈ M, I₁ ω ⊆ M
  /-- `M` is a union of cells of agent 2. -/
  closed₂ : ∀ ω ∈ M, I₂ ω ⊆ M

section Key

variable (p : Ω → ℝ) (I : Ω → Finset Ω) (E : Finset Ω) (q : ℝ)

/-- **Key aggregation lemma.**  If an event `M` is a union of cells of the partition `I`, and the
conditional probability of `E` given each such cell equals `q` (in multiplied form), then the
conditional probability of `E` given `M` equals `q` as well. -/
