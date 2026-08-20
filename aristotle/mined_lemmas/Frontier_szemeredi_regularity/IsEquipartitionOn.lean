import Mathlib

/-!
# Szemeredi Regularity
Category: Frontier Abel
Target: Frontier.szemeredi_regularity
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

set_option grind.warning false

namespace Frontier

open Finset

/-- `IsRegularPair G eps U V` says that the pair of vertex sets `(U, V)` is `ε`-regular
(`ε`-uniform) in the graph `G`: the edge density between any pair of sufficiently large
subsets `A ⊆ U`, `B ⊆ V` differs from the density between `U` and `V` by less than `ε`. -/

def IsEquipartitionOn {α : Type} [DecidableEq α] [Fintype α] (parts : Finset (Finset α)) : Prop :=
  (∀ U ∈ parts, U.Nonempty) ∧
  (∀ U ∈ parts, ∀ V ∈ parts, U ≠ V → Disjoint U V) ∧
  (∀ v : α, ∃ U ∈ parts, v ∈ U) ∧
  (∀ U ∈ parts, ∀ V ∈ parts, #U ≤ #V + 1)

/-- **Szemerédi's Regularity Lemma.**  For every `ε > 0` and every `l` there is a bound `M`,
depending only on `ε` and `l` (not on the graph), such that every finite graph on at least `l`
vertices admits an equipartition of its vertex set into at least `l` and at most `M` parts, all
but at most an `ε`-fraction of whose pairs of distinct parts are `ε`-regular. -/
