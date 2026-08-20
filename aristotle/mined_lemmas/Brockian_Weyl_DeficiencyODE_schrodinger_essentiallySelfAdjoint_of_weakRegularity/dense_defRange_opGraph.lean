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

lemma dense_defRange_opGraph [CompleteSpace H] {S : H →L[ℂ] H}
    (hS : ∀ x y : H, ⟪S x, y⟫_ℂ = ⟪x, S y⟫_ℂ) {D : Submodule ℂ H} (hD : Dense (D : Set H))
    {c : ℂ} (hc : c.re = 0) (hc0 : c ≠ 0) :
    Dense ((defRange c (opGraph S D) : Submodule ℂ H) : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro z hz
  have hzero : ∀ x : H, ⟪S x + c • x, z⟫_ℂ = 0 := by
    have hclosed : IsClosed {x : H | ⟪S x + c • x, z⟫_ℂ = 0} :=
      isClosed_eq (((S.continuous).add (continuous_const_smul c)).inner continuous_const)
        continuous_const
    have hsub : (D : Set H) ⊆ {x : H | ⟪S x + c • x, z⟫_ℂ = 0} := by
      intro x hx
      exact hz _ (mem_defRange_iff.mpr ⟨(x, S x), ⟨hx, rfl⟩, rfl⟩)
    intro x
    have huniv : (Set.univ : Set H) ⊆ {x : H | ⟪S x + c • x, z⟫_ℂ = 0} := by
      rw [← hD.closure_eq]
      exact hclosed.closure_subset_iff.mpr hsub
    exact huniv (Set.mem_univ x)
  have hzz := hzero z
  rw [inner_add_left, inner_smul_left] at hzz
  have hreal : (⟪S z, z⟫_ℂ).im = 0 := by
    have hconj : (starRingEnd ℂ) ⟪S z, z⟫_ℂ = ⟪S z, z⟫_ℂ := by
      rw [inner_conj_symm]; exact (hS z z).symm
    have h2 := congrArg Complex.im hconj
    simp only [Complex.conj_im] at h2
    linarith
  have hnormsq : ⟪z, z⟫_ℂ = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_num
  rw [hnormsq] at hzz
  have hconjc : (starRingEnd ℂ) c = -c := by
    apply Complex.ext <;> simp [hc]
  rw [hconjc] at hzz
  have hcim : c.im ≠ 0 := by
    intro h
    exact hc0 (Complex.ext hc h)
  have him := congrArg Complex.im hzz
  simp only [Complex.add_im, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.zero_im, hreal] at him
  have hnorm2 : (‖z‖ : ℝ) ^ 2 = 0 := by
    rcases lt_or_gt_of_ne hcim with h | h <;> nlinarith [him]
  have hz0 : ‖z‖ = 0 := by nlinarith [norm_nonneg z]
  exact norm_eq_zero.mp hz0

/-- A bounded symmetric operator is essentially self-adjoint on any dense core. -/
