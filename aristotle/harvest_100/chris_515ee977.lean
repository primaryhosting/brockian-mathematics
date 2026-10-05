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

/-- The density of edges of `G` between two finsets of vertices `s` and `t`:
the number of pairs `(a, b) ∈ s × t` with `a` adjacent to `b`, divided by `#s * #t`. -/
noncomputable def density {α : Type*} [DecidableEq α] (G : SimpleGraph α) (s t : Finset α) : ℝ :=
  (#{p ∈ s ×ˢ t | G.Adj p.1 p.2} : ℝ) / ((#s : ℝ) * (#t : ℝ))

/-- A pair of finsets `(s, t)` of vertices is `ε`-regular in `G` when the edge density between
any pair of subsets `s' ⊆ s`, `t' ⊆ t` with `#s' ≥ ε * #s` and `#t' ≥ ε * #t` differs from the
edge density between `s` and `t` by less than `ε`. -/
def IsRegularPair {α : Type*} [DecidableEq α] (G : SimpleGraph α) (ε : ℝ) (s t : Finset α) :
    Prop :=
  ∀ s' ⊆ s, ∀ t' ⊆ t, ε * (#s : ℝ) ≤ (#s' : ℝ) → ε * (#t : ℝ) ≤ (#t' : ℝ) →
    |density G s' t' - density G s t| < ε

section aux

variable {α : Type*} [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]

/-- The explicit density agrees with Mathlib's rational-valued edge density. -/
lemma density_eq_edgeDensity (s t : Finset α) :
    density G s t = ((G.edgeDensity s t : ℚ) : ℝ) := by
  rw [density, SimpleGraph.edgeDensity_def, SimpleGraph.interedges_def]
  push_cast
  congr 3
  ext p
  simp

/-- Mathlib's `SimpleGraph.IsUniform` (over `ℝ`) coincides with `IsRegularPair`. -/
lemma isUniform_iff_isRegularPair (ε : ℝ) (s t : Finset α) :
    G.IsUniform ε s t ↔ IsRegularPair G ε s t := by
  constructor
  · intro h s' hs' t' ht' hs ht
    have := h hs' ht' (by rwa [mul_comm]) (by rwa [mul_comm])
    rw [density_eq_edgeDensity, density_eq_edgeDensity]
    simpa using this
  · intro h s' hs' t' ht' hs ht
    have := h s' hs' t' ht' (by rwa [mul_comm]) (by rwa [mul_comm])
    rw [density_eq_edgeDensity, density_eq_edgeDensity] at this
    simpa using this

end aux

/-- **Szemerédi's Regularity Lemma**.

For every `ε > 0` and every `l`, there is a bound `M` (depending only on `ε` and `l`, not on the
graph) such that every finite graph `G` on at least `l` vertices admits a partition of its vertex
set into between `l` and `M` nonempty parts, which is an equipartition (any two parts differ in
size by at most one), and for which the number of ordered pairs of distinct parts that fail to be
`ε`-regular is at most `ε` times the square of the number of parts. -/
theorem szemeredi_regularity (ε : ℝ) (hε : 0 < ε) (l : ℕ) :
    ∃ M : ℕ, ∀ (α : Type) [DecidableEq α] [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj],
      l ≤ Fintype.card α →
        ∃ parts : Finset (Finset α),
          (∀ A ∈ parts, A.Nonempty) ∧
          (∀ A ∈ parts, ∀ B ∈ parts, A ≠ B → Disjoint A B) ∧
          (∀ v : α, ∃ A ∈ parts, v ∈ A) ∧
          l ≤ #parts ∧ #parts ≤ M ∧
          (∀ A ∈ parts, ∀ B ∈ parts, #A ≤ #B + 1) ∧
          ((#{p ∈ parts ×ˢ parts | p.1 ≠ p.2 ∧ ¬ IsRegularPair G ε p.1 p.2} : ℝ)
            ≤ ε * (#parts : ℝ) ^ 2) := by
  refine ⟨SzemerediRegularity.bound ε l, ?_⟩
  intro α _ _ G _ hl
  obtain ⟨P, hPeq, hPl, hPM, hPu⟩ := _root_.szemeredi_regularity G hε hl
  refine ⟨P.parts, fun A hA => P.nonempty_of_mem_parts hA, ?_, ?_, hPl, hPM, ?_, ?_⟩
  · intro A hA B hB hAB
    exact P.disjoint hA hB hAB
  · intro v
    obtain ⟨A, hA, hv⟩ := P.exists_mem (Finset.mem_univ v)
    exact ⟨A, hA, hv⟩
  · intro A hA B hB
    exact hPeq hA hB
  · -- the nonuniformity count
    have hset : {p ∈ P.parts ×ˢ P.parts | p.1 ≠ p.2 ∧ ¬ IsRegularPair G ε p.1 p.2}
        = P.nonUniforms G ε := by
      ext p
      simp only [Finpartition.nonUniforms, Finset.mem_filter, Finset.mem_product,
        Finset.mem_offDiag, isUniform_iff_isRegularPair]
      tauto
    rw [hset]
    refine hPu.trans ?_
    have h1 : ((#P.parts * (#P.parts - 1) : ℕ) : ℝ) ≤ (#P.parts : ℝ) ^ 2 := by
      have : (#P.parts * (#P.parts - 1) : ℕ) ≤ #P.parts ^ 2 := by
        calc (#P.parts * (#P.parts - 1) : ℕ) ≤ #P.parts * #P.parts :=
              Nat.mul_le_mul_left _ (Nat.sub_le _ _)
          _ = #P.parts ^ 2 := by ring
      exact_mod_cast this
    rw [mul_comm ε]
    exact mul_le_mul_of_nonneg_right h1 hε.le

end Frontier

