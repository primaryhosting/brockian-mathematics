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

theorem essentiallySelfAdjoint_perturbGraph [CompleteSpace H] {G : OperatorGraph H}
    (hG : EssentiallySelfAdjoint G) {V : H →L[ℂ] H}
    (hV : ∀ x y : H, ⟪V x, y⟫_ℂ = ⟪x, V y⟫_ℂ) :
    EssentiallySelfAdjoint (perturbGraph V G) := by
  have hsym : IsSymmetricGraph G :=
    le_trans (Submodule.le_topologicalClosure G) (le_of_eq hG)
  set c : ℂ := ((‖V‖ + 1 : ℝ) : ℂ) * Complex.I with hcdef
  have hcre : c.re = 0 := by simp [hcdef]
  have hcnorm : ‖c‖ = ‖V‖ + 1 := by
    rw [hcdef, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖V‖ + 1)]
  have hlt : ‖V‖ < ‖c‖ := by rw [hcnorm]; linarith
  have hc0 : c ≠ 0 := by
    intro h
    rw [h] at hcnorm
    simp at hcnorm
    linarith [norm_nonneg V]
  have hKsa : IsSelfAdjointGraph G.topologicalClosure := isSelfAdjointGraph_topologicalClosure hG
  refine essentiallySelfAdjoint_of_defRange_dense (isSymmetricGraph_perturbGraph hsym hV)
    hcre hc0 ?_ ?_
  · exact dense_defRange_perturbGraph (defRange_perturbGraph_eq_top hKsa hcre hc0 hlt)
  · refine dense_defRange_perturbGraph (defRange_perturbGraph_eq_top hKsa ?_ ?_ ?_)
    · simpa using hcre
    · exact neg_ne_zero.mpr hc0
    · simpa using hlt

/-! ### The Schrödinger operator -/

/-- The Schrödinger operator with bounded kinetic term `A` and bounded potential `V`. -/
