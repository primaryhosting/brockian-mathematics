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
noncomputable def density {α : Type*} (G : SimpleGraph α) (A B : Finset α) : ℝ :=
  (#{p ∈ A ×ˢ B | G.Adj p.1 p.2} : ℝ) / (#A * #B)

/-- A pair of vertex sets `(A, B)` is `ε`-regular for `G` when the density between any pair of
sufficiently large subsets `A' ⊆ A`, `B' ⊆ B` differs from the density between `A` and `B` by
less than `ε`. -/
def IsRegularPair {α : Type*} (G : SimpleGraph α) (ε : ℝ) (A B : Finset α) : Prop :=
  ∀ A' ⊆ A, ∀ B' ⊆ B, ε * #A ≤ #A' → ε * #B ≤ #B' →
    |density G A' B' - density G A B| < ε

/-- `Frontier.density` agrees with Mathlib's `SimpleGraph.edgeDensity`. -/
theorem density_eq_edgeDensity {α : Type*} [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (A B : Finset α) :
    density G A B = ((G.edgeDensity A B : ℚ) : ℝ) := by
  simp only [density, SimpleGraph.edgeDensity_def, SimpleGraph.interedges_def]
  push_cast
  refine congrArg (fun n : ℕ => (n : ℝ) / ((#A : ℝ) * (#B : ℝ))) ?_
  congr

/-- `Frontier.IsRegularPair` agrees with Mathlib's `SimpleGraph.IsUniform` over `ℝ`. -/
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
theorem szemeredi_regularity {ε : ℝ} (hε : 0 < ε) (l : ℕ) :
    ∃ M : ℕ, ∀ (α : Type*) [DecidableEq α] [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj],
      l ≤ Fintype.card α →
      ∃ P : Finset (Finset α),
        (∀ A ∈ P, A.Nonempty) ∧
        (∀ v : α, ∃! A : Finset α, A ∈ P ∧ v ∈ A) ∧
        (∀ A ∈ P, ∀ B ∈ P, #A ≤ #B + 1) ∧
        l ≤ #P ∧ #P ≤ M ∧
        ((#{AB ∈ P.offDiag | ¬ IsRegularPair G ε AB.1 AB.2} : ℝ) ≤ ε * (#P : ℝ) ^ 2) := by
  classical
  refine ⟨SzemerediRegularity.bound ε l, ?_⟩
  intro α _ _ G _ hl
  obtain ⟨P, hPeq, hPl, hPM, hPu⟩ := _root_.szemeredi_regularity (ε := ε) G hε hl
  refine ⟨P.parts, fun A hA => P.nonempty_of_mem_parts hA, ?_, ?_, hPl, hPM, ?_⟩
  · intro v
    obtain ⟨A, hA, hvA⟩ := P.exists_mem (Finset.mem_univ v)
    exact ⟨A, ⟨hA, hvA⟩, fun B hB => P.eq_of_mem_parts hB.1 hA hB.2 hvA⟩
  · intro A hA B hB
    by_contra hc
    exact absurd hPeq (Finpartition.not_isEquipartition.2 ⟨A, hA, B, hB, by omega⟩)
  · have hset : {AB ∈ P.parts.offDiag | ¬ IsRegularPair G ε AB.1 AB.2}
        = P.nonUniforms G ε := by
      unfold Finpartition.nonUniforms
      apply Finset.filter_congr
      intro AB _
      simp [isRegularPair_iff_isUniform]
    rw [hset]
    refine hPu.trans ?_
    have h1 : ((#P.parts * (#P.parts - 1) : ℕ) : ℝ) ≤ (#P.parts : ℝ) ^ 2 := by
      have : (#P.parts * (#P.parts - 1) : ℕ) ≤ #P.parts ^ 2 := by
        rcases Nat.eq_zero_or_pos #P.parts with h | h
        · simp [h]
        · calc #P.parts * (#P.parts - 1) ≤ #P.parts * #P.parts := by
                exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
            _ = #P.parts ^ 2 := by ring
      exact_mod_cast this
    calc ((#P.parts * (#P.parts - 1) : ℕ) : ℝ) * ε ≤ (#P.parts : ℝ) ^ 2 * ε := by
          exact mul_le_mul_of_nonneg_right h1 hε.le
      _ = ε * (#P.parts : ℝ) ^ 2 := by ring

end Frontier

