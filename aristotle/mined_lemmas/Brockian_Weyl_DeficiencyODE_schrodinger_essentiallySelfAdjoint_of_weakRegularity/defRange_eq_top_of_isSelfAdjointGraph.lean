import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
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

open scoped InnerProductSpace
open scoped NNReal

namespace Brockian.Weyl.DeficiencyODE

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An (in general unbounded) linear operator on a Hilbert space `H` is encoded by its graph,
a linear subspace of `H × H`. -/
abbrev OperatorGraph (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  Submodule ℂ (H × H)

/-- The graph of the adjoint of the operator with graph `G`:
`(u, v)` belongs to it iff `⟪T x, u⟫ = ⟪x, v⟫` for all `(x, T x) ∈ G`. -/

lemma defRange_eq_top_of_isSelfAdjointGraph [CompleteSpace H] {K : OperatorGraph H}
    (hK : IsSelfAdjointGraph K) {c : ℂ} (hc : c.re = 0) (hc0 : c ≠ 0) :
    defRange c K = ⊤ := by
  have hsym : IsSymmetricGraph K := hK.isSymmetric
  have hKclosed : IsClosed ((K : OperatorGraph H) : Set (H × H)) := hK.isClosed
  have hconjc : (starRingEnd ℂ) c = -c := by
    apply Complex.ext <;> simp [hc]
  have hrangeClosed : IsClosed ((defRange c K : Submodule ℂ H) : Set H) :=
    isClosed_defRange hsym hKclosed hc hc0
  have hdense : Dense ((defRange c K : Submodule ℂ H) : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
      Submodule.eq_bot_iff]
    intro z hz
    have hmem : ((z, c • z) : H × H) ∈ adjointGraph K := by
      intro q hq
      have h0 : ⟪q.2 + c • q.1, z⟫_ℂ = 0 := hz _ (mem_defRange_iff.mpr ⟨q, hq, rfl⟩)
      rw [inner_add_left, inner_smul_left, hconjc] at h0
      show ⟪q.2, z⟫_ℂ = ⟪q.1, c • z⟫_ℂ
      rw [inner_smul_right]
      linear_combination h0
    rw [hK] at hmem
    have hsymz := hsym hmem ((z, c • z) : H × H) hmem
    simp only [inner_smul_left, inner_smul_right, hconjc] at hsymz
    have h2 : (2 * c) * ⟪z, z⟫_ℂ = 0 := by linear_combination -hsymz
    have hc2 : (2 : ℂ) * c ≠ 0 := by
      simp [hc0]
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hc2
    · exact inner_self_eq_zero.mp h
  have hall : ((defRange c K : Submodule ℂ H) : Set H) = Set.univ := by
    rw [← hdense.closure_eq, hrangeClosed.closure_eq]
  refine eq_top_iff.mpr ?_
  intro z _
  have : z ∈ ((defRange c K : Submodule ℂ H) : Set H) := by rw [hall]; trivial
  exact this

/-- The map `(x, y) ↦ (x, y + V x)` implementing the perturbation of an operator by a bounded
operator `V`. -/
