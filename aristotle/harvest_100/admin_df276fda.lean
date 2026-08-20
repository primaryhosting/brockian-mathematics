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
def IsEquipartitionOn {α : Type} [DecidableEq α] [Fintype α] (parts : Finset (Finset α)) : Prop :=
  (∀ U ∈ parts, U.Nonempty) ∧
  (∀ U ∈ parts, ∀ V ∈ parts, U ≠ V → Disjoint U V) ∧
  (∀ v : α, ∃ U ∈ parts, v ∈ U) ∧
  (∀ U ∈ parts, ∀ V ∈ parts, #U ≤ #V + 1)

/-- **Szemerédi's Regularity Lemma.**  For every `ε > 0` and every `l` there is a bound `M`,
depending only on `ε` and `l` (not on the graph), such that every finite graph on at least `l`
vertices admits an equipartition of its vertex set into at least `l` and at most `M` parts, all
but at most an `ε`-fraction of whose pairs of distinct parts are `ε`-regular. -/
theorem szemeredi_regularity (eps : ℝ) (heps : 0 < eps) (l : ℕ) :
    ∃ M : ℕ, ∀ (α : Type) [DecidableEq α] [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj],
      l ≤ Fintype.card α →
      ∃ parts : Finset (Finset α),
        IsEquipartitionOn parts ∧ l ≤ #parts ∧ #parts ≤ M ∧
        ((#{UV ∈ parts.offDiag | ¬ IsRegularPair G eps UV.1 UV.2} : ℝ)
          ≤ eps * (#parts * (#parts - 1))) := by
  refine ⟨SzemerediRegularity.bound eps l, ?_⟩
  intro α _ _ G _ hl
  obtain ⟨P, hPeq, hPl, hPM, hPu⟩ := _root_.szemeredi_regularity G heps hl
  refine ⟨P.parts, ⟨?_, ?_, ?_, ?_⟩, hPl, hPM, ?_⟩
  · intro U hU
    exact P.nonempty_of_mem_parts hU
  · intro U hU V hV hUV
    exact P.disjoint hU hV hUV
  · intro v
    obtain ⟨U, hU, hvU⟩ := P.exists_mem (Finset.mem_univ v)
    exact ⟨U, hU, hvU⟩
  · intro U hU V hV
    exact hPeq hU hV
  · -- translate Mathlib's `Finpartition.IsUniform` into the explicit form
    have hset : {UV ∈ P.parts.offDiag | ¬ IsRegularPair G eps UV.1 UV.2}
        = P.nonUniforms G eps := by
      unfold Finpartition.nonUniforms
      apply Finset.filter_congr
      rintro ⟨U, V⟩ -
      constructor
      · intro h hu
        exact h fun A hA B hB h1 h2 => hu hA hB h1 h2
      · intro h hu
        exact h fun A hA B hB h1 h2 => hu A hA B hB h1 h2
    rw [hset]
    refine hPu.trans ?_
    rw [mul_comm]
    gcongr
    rcases Nat.eq_zero_or_pos (#P.parts) with h | h
    · simp [h]
    · have : ((#P.parts * (#P.parts - 1) : ℕ) : ℝ) = (#P.parts : ℝ) * ((#P.parts : ℝ) - 1) := by
        push_cast [Nat.cast_sub h]
        ring
      rw [this]

end Frontier

