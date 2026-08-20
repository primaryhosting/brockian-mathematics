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

/-- **Szemerédi's Regularity Lemma** (equipartition version).

For every `ε > 0` and every natural number `l`, there is a bound `M = SzemerediRegularity.bound ε l`
(depending only on `ε` and `l`, not on the graph) such that every finite simple graph `G` on a
vertex type `α` with at least `l` vertices admits an equipartition `P` of its vertex set into at
least `l` and at most `M` parts which is `ε`-uniform for `G`.

This is proved by appealing to Mathlib's `szemeredi_regularity`
(`Mathlib/Combinatorics/SimpleGraph/Regularity/Lemma.lean`, due to Yaël Dillies and Bhavik Mehta). -/
theorem szemeredi_regularity {α : Type*} [DecidableEq α] [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj] {ε : ℝ} {l : ℕ}
    (hε : 0 < ε) (hl : l ≤ Fintype.card α) :
    ∃ P : Finpartition (Finset.univ : Finset α),
      P.IsEquipartition ∧ l ≤ P.parts.card ∧ P.parts.card ≤ SzemerediRegularity.bound ε l ∧
        P.IsUniform G ε :=
  _root_.szemeredi_regularity G hε hl

end Frontier

