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

theorem essentiallySelfAdjoint_of_defRange_dense [CompleteSpace H] {G : OperatorGraph H}
    (hsym : IsSymmetricGraph G) {c : ℂ} (hc : c.re = 0) (hc0 : c ≠ 0)
    (hplus : Dense ((defRange c G : Submodule ℂ H) : Set H))
    (hminus : Dense ((defRange (-c) G : Submodule ℂ H) : Set H)) :
    EssentiallySelfAdjoint G := by
  refine le_antisymm (closure_le_adjointGraph hsym) ?_
  intro p hp
  obtain ⟨q, hq, hqeq⟩ : ∃ q ∈ G.topologicalClosure,
      q.2 + (-c) • q.1 = p.2 + (-c) • p.1 := by
    have htop := defRange_closure_eq_top hsym (by simpa using hc) (neg_ne_zero.mpr hc0) hminus
    have hmem : (p.2 + (-c) • p.1) ∈ defRange (-c) G.topologicalClosure := by
      rw [htop]; trivial
    exact mem_defRange_iff.mp hmem
  set a : H × H := p - q with ha
  have ha2 : a.2 = c • a.1 := by
    have h := hqeq
    simp only [neg_smul] at h
    have hkey : p.2 - q.2 = c • (p.1 - q.1) := by
      rw [smul_sub]
      linear_combination (norm := module) -h
    simpa [ha] using hkey
  have hconjc : (starRingEnd ℂ) c = -c := by
    apply Complex.ext <;> simp [hc]
  have haadj : a ∈ adjointGraph G :=
    (adjointGraph G).sub_mem hp (closure_le_adjointGraph hsym hq)
  have ha1 : a.1 = 0 := by
    have horth : ((defRange c G : Submodule ℂ H) : Set H)
        ⊆ {z : H | ⟪z, a.1⟫_ℂ = 0} := by
      intro z hz
      obtain ⟨r, hr, rfl⟩ := mem_defRange_iff.mp hz
      have h1 : ⟪r.2, a.1⟫_ℂ = c * ⟪r.1, a.1⟫_ℂ := by
        have := haadj r hr
        rw [ha2, inner_smul_right] at this
        exact this
      simp only [Set.mem_setOf_eq, inner_add_left, inner_smul_left, h1, hconjc]
      ring
    have hclosed : IsClosed {z : H | ⟪z, a.1⟫_ℂ = 0} :=
      isClosed_eq (continuous_id.inner continuous_const) continuous_const
    have hall : ∀ z : H, ⟪z, a.1⟫_ℂ = 0 := by
      intro z
      have hsub : (Set.univ : Set H) ⊆ {z : H | ⟪z, a.1⟫_ℂ = 0} := by
        rw [← hplus.closure_eq]
        exact hclosed.closure_subset_iff.mpr horth
      exact hsub (Set.mem_univ z)
    exact inner_self_eq_zero.mp (hall a.1)
  have ha0 : a = 0 := by
    have : a.2 = 0 := by rw [ha2, ha1, smul_zero]
    exact Prod.ext ha1 this
  have : p = q := by
    have := ha0
    rw [ha, sub_eq_zero] at this
    exact this
  rw [this]
  exact hq

/-! ### Bounded symmetric operators restricted to a dense core -/

/-- The graph of the bounded operator `S` restricted to the subspace `D`. -/
