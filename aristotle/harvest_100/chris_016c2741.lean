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

open Finset

namespace Frontier

variable {α : Type*}

/-- The edge density between two finsets of vertices `s` and `t` of a graph `G`: the number of
pairs `(x, y) ∈ s × t` with `x` adjacent to `y`, divided by `#s * #t`. -/
noncomputable def dens (G : SimpleGraph α) [DecidableRel G.Adj] (s t : Finset α) : ℝ :=
  (#{p ∈ s ×ˢ t | G.Adj p.1 p.2} : ℝ) / ((#s : ℝ) * (#t : ℝ))

/-- A pair of finsets of vertices `(s, t)` is `ε`-uniform (`ε`-regular) in `G` when the edge
density between any pair of sufficiently large subsets `s' ⊆ s`, `t' ⊆ t` is within `ε` of the
edge density between `s` and `t`. -/
def IsUnifPair (G : SimpleGraph α) [DecidableRel G.Adj] (ε : ℝ) (s t : Finset α) : Prop :=
  ∀ s' ⊆ s, ∀ t' ⊆ t, (#s : ℝ) * ε ≤ #s' → (#t : ℝ) * ε ≤ #t' →
    |dens G s' t' - dens G s t| < ε

/-- `dens` agrees with Mathlib's rational-valued `SimpleGraph.edgeDensity`. -/
theorem dens_eq_edgeDensity (G : SimpleGraph α) [DecidableRel G.Adj] (s t : Finset α) :
    dens G s t = ((G.edgeDensity s t : ℚ) : ℝ) := by
  rw [dens, SimpleGraph.edgeDensity_def, ← SimpleGraph.interedges_def, Rat.cast_div]
  push_cast
  ring

/-- `IsUnifPair` agrees with Mathlib's `SimpleGraph.IsUniform` over `ℝ`. -/
theorem isUnifPair_iff (G : SimpleGraph α) [DecidableRel G.Adj] (ε : ℝ) (s t : Finset α) :
    IsUnifPair G ε s t ↔ G.IsUniform ε s t := by
  simp only [IsUnifPair, SimpleGraph.IsUniform, dens_eq_edgeDensity]

open scoped Classical in
/-- **Szemerédi's Regularity Lemma**.

For every `ε > 0` and every `l`, there is a bound `M`, depending only on `ε` and `l` (and not on
the graph nor on the number of vertices), such that every finite graph `G` on at least `l`
vertices admits a partition of its vertex set into between `l` and `M` nonempty parts which is
* an *equipartition*: any two parts have sizes differing by at most one, and
* `ε`-*regular*: the number of ordered pairs of distinct parts `(A, B)` that fail to be
  `ε`-uniform is at most `ε * (number of parts)²`. -/
theorem szemeredi_regularity (ε : ℝ) (hε : 0 < ε) (l : ℕ) :
    ∃ M : ℕ, ∀ (α : Type) [DecidableEq α] [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj],
      l ≤ Fintype.card α →
        ∃ P : Finset (Finset α),
          (∀ A ∈ P, A.Nonempty) ∧
          ((P : Set (Finset α)).PairwiseDisjoint id) ∧
          (∀ x : α, ∃ A ∈ P, x ∈ A) ∧
          l ≤ #P ∧ #P ≤ M ∧
          (∀ A ∈ P, ∀ B ∈ P, #A ≤ #B + 1) ∧
          (#{q ∈ P ×ˢ P | q.1 ≠ q.2 ∧ ¬ IsUnifPair G ε q.1 q.2} : ℝ) ≤ ε * (#P : ℝ) ^ 2 := by
  classical
  refine ⟨SzemerediRegularity.bound ε l, ?_⟩
  intro α _ _ G _ hcard
  obtain ⟨P, hequi, hl, hM, hunif⟩ := _root_.szemeredi_regularity G hε hcard
  refine ⟨P.parts, fun A hA => P.nonempty_of_mem_parts hA, P.disjoint, ?_, hl, hM, ?_, ?_⟩
  · intro x
    obtain ⟨A, hA, hx⟩ := P.exists_mem (Finset.mem_univ x)
    exact ⟨A, hA, hx⟩
  · intro A hA B hB
    exact hequi hA hB
  · have hset : {q ∈ P.parts ×ˢ P.parts | q.1 ≠ q.2 ∧ ¬ IsUnifPair G ε q.1 q.2}
        = P.nonUniforms G ε := by
      ext ⟨u, v⟩
      simp [Finpartition.nonUniforms, Finset.mem_offDiag, isUnifPair_iff, and_assoc]
    rw [hset]
    refine hunif.trans ?_
    have hn : ((#P.parts * (#P.parts - 1) : ℕ) : ℝ) ≤ (#P.parts : ℝ) ^ 2 := by
      have : (#P.parts * (#P.parts - 1) : ℕ) ≤ #P.parts ^ 2 := by
        rw [sq]
        exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      exact_mod_cast this
    calc ((#P.parts * (#P.parts - 1) : ℕ) : ℝ) * ε ≤ (#P.parts : ℝ) ^ 2 * ε :=
          mul_le_mul_of_nonneg_right hn hε.le
      _ = ε * (#P.parts : ℝ) ^ 2 := by ring

end Frontier

import Mathlib
import RequestProject.SzemerediRegularity

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

