/-
# Szemeredi Regularity
Category: Frontier Abel
Target: Frontier.szemeredi_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Szemeredi Regularity
Category: Frontier Abel
Target: Frontier.szemeredi_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finpartition Finset Fintype Function SzemerediRegularity

namespace Frontier

/-- **Szemerédi's Regularity Lemma** (equipartition version): for every `ε > 0` and every
`l ≤ card α`, any finite simple graph `G` on a finite vertex type `α` admits a partition `P` of
the vertex set which is an equipartition (all parts have the same size up to a difference of one),
has at least `l` and at most `SzemerediRegularity.bound ε l` parts, and is `ε`-uniform for `G`.
The bound depends only on `ε` and `l`, not on the graph.

This is Mathlib's `szemeredi_regularity`
(`Mathlib/Combinatorics/SimpleGraph/Regularity/Lemma.lean`, by Yaël Dillies and Bhavik Mehta). -/
theorem szemeredi_regularity {α : Type*} [DecidableEq α] [Fintype α] (G : SimpleGraph α)
    [DecidableRel G.Adj] {ε : ℝ} {l : ℕ} (hε : 0 < ε) (hl : l ≤ card α) :
    ∃ P : Finpartition (univ : Finset α),
      P.IsEquipartition ∧ l ≤ #P.parts ∧ #P.parts ≤ SzemerediRegularity.bound ε l ∧
        P.IsUniform G ε :=
  _root_.szemeredi_regularity G hε hl

end Frontier

import Mathlib

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

