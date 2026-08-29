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

open scoped Classical in
/-- The edge density between two finsets of vertices `u`, `v` of a graph `G`: the number of
adjacent pairs `(a, b) ∈ u ×ˢ v`, divided by `#u * #v`. -/
noncomputable def edgeDens {α : Type*} (G : SimpleGraph α) (u v : Finset α) : ℝ :=
  (#{e ∈ u ×ˢ v | G.Adj e.1 e.2} : ℝ) / (#u * #v)

/-- A pair `(u, v)` of finsets of vertices is `ε`-regular (`ε`-uniform) for `G` when the edge
density between any pair of subsets `u' ⊆ u`, `v' ⊆ v` that are not too small (of size at least
`ε * #u` resp. `ε * #v`) is within `ε` of the edge density between `u` and `v`. -/
def IsRegularPair {α : Type*} (G : SimpleGraph α) (ε : ℝ) (u v : Finset α) : Prop :=
  ∀ u' ⊆ u, ∀ v' ⊆ v, (#u : ℝ) * ε ≤ #u' → (#v : ℝ) * ε ≤ #v' →
    |edgeDens G u' v' - edgeDens G u v| < ε

end Frontier

section Auxiliary

variable {α : Type*} (G : SimpleGraph α) [DecidableRel G.Adj]

/-- `Frontier.edgeDens` agrees with Mathlib's `SimpleGraph.edgeDensity`. -/
theorem Frontier.edgeDens_eq (u v : Finset α) :
    Frontier.edgeDens G u v = (G.edgeDensity u v : ℝ) := by
  classical
  rw [Frontier.edgeDens, SimpleGraph.edgeDensity, Rel.edgeDensity, Rat.cast_div]
  push_cast
  congr 4

/-- `Frontier.IsRegularPair` agrees with Mathlib's `SimpleGraph.IsUniform`. -/
theorem Frontier.isRegularPair_iff (ε : ℝ) (u v : Finset α) :
    Frontier.IsRegularPair G ε u v ↔ G.IsUniform ε u v := by
  constructor
  · intro h u' hu' v' hv' hu hv
    simpa [Frontier.edgeDens_eq] using h u' hu' v' hv' hu hv
  · intro h u' hu' v' hv' hu hv
    simpa [Frontier.edgeDens_eq] using h hu' hv' hu hv

end Auxiliary

namespace Frontier

open scoped Classical in
/-- **Szemerédi's Regularity Lemma.**

For every `ε > 0` and every `l : ℕ` there is a bound `M`, depending only on `ε` and `l`, such that
every finite simple graph `G` on at least `l` vertices admits a partition of its vertex set into
`parts` such that:

* every part is nonempty and every vertex lies in exactly one part (so `parts` is a partition);
* the partition is *equitable*: any two parts differ in size by at most one;
* the number of parts is between `l` and `M`;
* all but at most `ε * #parts ^ 2` of the ordered pairs of distinct parts are `ε`-regular.
-/
theorem szemeredi_regularity (ε : ℝ) (hε : 0 < ε) (l : ℕ) :
    ∃ M : ℕ, ∀ {α : Type*} [Fintype α] (G : SimpleGraph α), l ≤ Fintype.card α →
      ∃ parts : Finset (Finset α),
        (∀ p ∈ parts, p.Nonempty) ∧
        (∀ a : α, ∃! p, p ∈ parts ∧ a ∈ p) ∧
        (∀ p ∈ parts, ∀ q ∈ parts, #p ≤ #q + 1) ∧
        l ≤ #parts ∧ #parts ≤ M ∧
        (#{uv ∈ parts.offDiag | ¬ IsRegularPair G ε uv.1 uv.2} : ℝ) ≤ ε * #parts ^ 2 := by
  classical
  refine ⟨SzemerediRegularity.bound ε l, ?_⟩
  intro α _ G hl
  obtain ⟨P, hequi, hlP, hPM, hPU⟩ := _root_.szemeredi_regularity (ε := ε) G hε hl
  refine ⟨P.parts, fun p hp => P.nonempty_of_mem_parts hp,
    fun a => P.existsUnique_mem (mem_univ a), ?_, hlP, hPM, ?_⟩
  · intro p hp q hq
    exact hequi hp hq
  · have hfilter : {uv ∈ P.parts.offDiag | ¬ IsRegularPair G ε uv.1 uv.2}
        = P.nonUniforms G ε := by
      ext ⟨u, v⟩
      simp only [mem_filter, Finpartition.mk_mem_nonUniforms, mem_offDiag,
        Frontier.isRegularPair_iff]
      tauto
    rw [hfilter]
    refine hPU.trans ?_
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

