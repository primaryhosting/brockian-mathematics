/-
# Szemeredi Regularity
Category: Frontier Abel
Target: Frontier.szemeredi_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

open Finset

universe u

variable {α : Type u} [DecidableEq α]

/-- The edge density between two finsets of vertices `U`, `V` of a graph `G`: the number of
pairs `(u, v) ∈ U × V` with `u` adjacent to `v`, divided by `#U * #V`. -/
noncomputable def density (G : SimpleGraph α) (U V : Finset α) : ℝ :=
  (#{p ∈ U ×ˢ V | G.Adj p.1 p.2} : ℝ) / (#U * #V)

/-- A pair of finsets of vertices `U`, `V` is `ε`-regular (`ε`-uniform) for `G` when the edge
density between any pair of subsets `U' ⊆ U`, `V' ⊆ V` that are large (of size at least an
`ε`-fraction of `U`, resp. `V`) is within `ε` of the edge density between `U` and `V`. -/
def IsRegularPair (G : SimpleGraph α) (ε : ℝ) (U V : Finset α) : Prop :=
  ∀ U' ⊆ U, ∀ V' ⊆ V, (#U : ℝ) * ε ≤ #U' → (#V : ℝ) * ε ≤ #V' →
    |density G U' V' - density G U V| < ε

omit [DecidableEq α] in
/-- `Frontier.density` agrees with Mathlib's `SimpleGraph.edgeDensity`. -/
theorem density_eq_edgeDensity (G : SimpleGraph α) [DecidableRel G.Adj] (U V : Finset α) :
    density G U V = (G.edgeDensity U V : ℝ) := by
  rw [density, SimpleGraph.edgeDensity, Rel.edgeDensity]
  push_cast
  congr 3
  simp only [Rel.interedges]
  congr!

omit [DecidableEq α] in
/-- `Frontier.IsRegularPair` agrees with Mathlib's `SimpleGraph.IsUniform` over `ℝ`. -/
theorem isRegularPair_iff_isUniform (G : SimpleGraph α) [DecidableRel G.Adj] (ε : ℝ)
    (U V : Finset α) : IsRegularPair G ε U V ↔ G.IsUniform ε U V := by
  constructor
  · intro h U' hU' V' hV' hU hV
    simpa [density_eq_edgeDensity] using h U' hU' V' hV' hU hV
  · intro h U' hU' V' hV' hU hV
    simpa [density_eq_edgeDensity] using h hU' hV' hU hV

/-- **Szemerédi's Regularity Lemma.**

For every `ε > 0` and every `l`, there is a bound `M` (depending only on `ε` and `l`, not on the
graph) such that every finite graph `G` on at least `l` vertices admits a partition `P` of its
vertex set which is

* an *equipartition*: any two parts differ in size by at most one;
* of controlled size: at least `l` and at most `M` parts;
* *`ε`-regular*: the number of ordered pairs of distinct parts that fail to be an `ε`-regular
  pair is at most `ε * (number of parts)²`.
-/
theorem szemeredi_regularity (ε : ℝ) (hε : 0 < ε) (l : ℕ) :
    ∃ M : ℕ, ∀ (α : Type u) [DecidableEq α] [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj],
      l ≤ Fintype.card α →
        ∃ P : Finpartition (univ : Finset α),
          (∀ U ∈ P.parts, ∀ V ∈ P.parts, #U ≤ #V + 1) ∧
          l ≤ #P.parts ∧ #P.parts ≤ M ∧
          (#{UV ∈ P.parts.offDiag | ¬ IsRegularPair G ε UV.1 UV.2} : ℝ) ≤ ε * (#P.parts : ℝ) ^ 2 := by
  refine ⟨SzemerediRegularity.bound ε l, ?_⟩
  intro α _ _ G _ hl
  obtain ⟨P, hPeq, hPl, hPM, hPu⟩ := _root_.szemeredi_regularity G hε hl
  refine ⟨P, ?_, hPl, hPM, ?_⟩
  · intro U hU V hV
    exact hPeq (Finset.mem_coe.2 hU) (Finset.mem_coe.2 hV)
  · have hset : {UV ∈ P.parts.offDiag | ¬ IsRegularPair G ε UV.1 UV.2}
        = P.nonUniforms G ε := by
      rw [Finpartition.nonUniforms]
      apply Finset.filter_congr
      rintro ⟨U, V⟩ -
      simp [isRegularPair_iff_isUniform]
    rw [hset]
    refine hPu.trans ?_
    have h1 : ((#P.parts * (#P.parts - 1) : ℕ) : ℝ) ≤ (#P.parts : ℝ) ^ 2 := by
      have : (#P.parts * (#P.parts - 1) : ℕ) ≤ #P.parts ^ 2 := by
        calc #P.parts * (#P.parts - 1) ≤ #P.parts * #P.parts := by
              exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
          _ = #P.parts ^ 2 := by ring
      exact_mod_cast this
    calc ((#P.parts * (#P.parts - 1) : ℕ) : ℝ) * ε ≤ (#P.parts : ℝ) ^ 2 * ε := by
          exact mul_le_mul_of_nonneg_right h1 hε.le
      _ = ε * (#P.parts : ℝ) ^ 2 := by ring

end Frontier

#print axioms Frontier.szemeredi_regularity

