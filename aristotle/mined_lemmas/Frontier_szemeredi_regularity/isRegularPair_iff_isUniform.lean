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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Finset

/-- The edge density of a graph `G` between two finite sets of vertices `A` and `B`: the
proportion of pairs in `A × B` that are adjacent. -/

theorem isRegularPair_iff_isUniform {α : Type*} [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (ε : ℝ) (A B : Finset α) :
    IsRegularPair G ε A B ↔ G.IsUniform ε A B := by
  constructor
  · intro h A' hA' B' hB' hA hB
    have := h A' hA' B' hB' (by rw [mul_comm]; exact hA) (by rw [mul_comm]; exact hB)
    rwa [density_eq_edgeDensity, density_eq_edgeDensity] at this
  · intro h A' hA' B' hB' hA hB
    have := h hA' hB' (by rw [mul_comm]; exact hA) (by rw [mul_comm]; exact hB)
    rwa [density_eq_edgeDensity, density_eq_edgeDensity]

/-- **Szemerédi's Regularity Lemma.**

For every `ε > 0` and every `l`, there is a bound `M` (depending only on `ε` and `l`, not on the
graph) such that every finite graph `G` on at least `l` vertices admits a partition `P` of its
vertex set into between `l` and `M` nonempty parts, whose parts all have the same size up to `1`
(an equipartition), and such that all but at most an `ε`-fraction of the ordered pairs of distinct
parts are `ε`-regular. -/
