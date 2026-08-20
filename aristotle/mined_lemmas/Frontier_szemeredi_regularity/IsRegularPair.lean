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

def IsRegularPair {α : Type} (G : SimpleGraph α) [DecidableRel G.Adj] (eps : ℝ)
    (U V : Finset α) : Prop :=
  ∀ A ⊆ U, ∀ B ⊆ V, (#U : ℝ) * eps ≤ #A → (#V : ℝ) * eps ≤ #B →
    |(G.edgeDensity A B : ℝ) - (G.edgeDensity U V : ℝ)| < eps

/-- `IsEquipartitionOn parts` says that `parts` is a partition of the whole vertex type into
nonempty, pairwise disjoint parts whose sizes differ by at most one. -/
