import Mathlib

/-!
# Szemeredi Regularity
Category: Frontier Abel
Target: Frontier.szemeredi_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Frontier

/-- **Szemerédi's Regularity Lemma**.

For every `ε > 0` and every `l : ℕ` there is a bound `M`, depending only on `ε` and `l`
(and in particular *not* on the graph), such that every finite simple graph `G` on at least
`l` vertices admits a partition `P` of its vertex set which is

* an equipartition: any two parts have sizes differing by at most one,
* of size between `l` and `M`,
* `ε`-uniform: the number of pairs `(u, v)` of distinct parts that fail to be `ε`-uniform
  (i.e. for which there are large subsets `u' ⊆ u`, `v' ⊆ v` whose edge density is `ε`-far from
  that of `(u, v)`) is at most `ε * #P.parts * (#P.parts - 1)`.
-/

theorem szemeredi_regularity_regular_pairs (ε : ℝ) (hε : 0 < ε) (l : ℕ) :
    ∃ M : ℕ, ∀ {α : Type*} [DecidableEq α] [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj],
      l ≤ Fintype.card α →
      ∃ P : Finpartition (Finset.univ : Finset α),
        (∀ u ∈ P.parts, ∀ v ∈ P.parts, #u ≤ #v + 1) ∧
        l ≤ #P.parts ∧ #P.parts ≤ M ∧
        (1 - ε) * (#P.parts * (#P.parts - 1) : ℕ)
          ≤ (#{uv ∈ P.parts.offDiag |
              ∀ ⦃u'⦄, u' ⊆ uv.1 → ∀ ⦃v'⦄, v' ⊆ uv.2 → (#uv.1 : ℝ) * ε ≤ #u' →
                (#uv.2 : ℝ) * ε ≤ #v' →
                |(G.edgeDensity u' v' : ℝ) - (G.edgeDensity uv.1 uv.2 : ℝ)| < ε} : ℝ) := by
  classical
  obtain ⟨M, hM⟩ := szemeredi_regularity ε hε l
  refine ⟨M, ?_⟩
  intro α _ _ G _ hl
  obtain ⟨P, hPeq, hPl, hPM, hPu⟩ := hM G hl
  refine ⟨P, hPeq, hPl, hPM, ?_⟩
  set p : Finset α × Finset α → Prop := fun uv =>
    ∀ ⦃u'⦄, u' ⊆ uv.1 → ∀ ⦃v'⦄, v' ⊆ uv.2 → (#uv.1 : ℝ) * ε ≤ #u' → (#uv.2 : ℝ) * ε ≤ #v' →
      |(G.edgeDensity u' v' : ℝ) - (G.edgeDensity uv.1 uv.2 : ℝ)| < ε with hp
  have hsplit : #{uv ∈ P.parts.offDiag | p uv} + #{uv ∈ P.parts.offDiag | ¬ p uv}
      = #P.parts.offDiag := Finset.card_filter_add_card_filter_not _
  have hoff : #P.parts.offDiag = #P.parts * (#P.parts - 1) := by
    rw [Finset.offDiag_card, Nat.mul_sub_one]
  have hcast : (#{uv ∈ P.parts.offDiag | p uv} : ℝ) + (#{uv ∈ P.parts.offDiag | ¬ p uv} : ℝ)
      = ((#P.parts * (#P.parts - 1) : ℕ) : ℝ) := by
    rw [← Nat.cast_add, hsplit, hoff]
  nlinarith [hPu, hcast]

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

