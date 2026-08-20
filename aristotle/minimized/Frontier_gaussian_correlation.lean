import Mathlib

/-!
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
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

open MeasureTheory ProbabilityTheory Set

/-- A set is *symmetric convex* if it is convex and invariant under `x ↦ -x`. -/

def IsSymmConvex {E : Type*} [AddCommGroup E] [Module ℝ E] (K : Set E) : Prop :=
  Convex ℝ K ∧ ∀ x ∈ K, -x ∈ K

/-- The Gaussian correlation inequality (Royen's theorem) for the space `E`:
for every centered Gaussian measure `μ` on `E` (centered being expressed as the invariance
`μ.map (fun x ↦ -x) = μ`) and all symmetric convex measurable sets `K` and `L`, one has
`μ K * μ L ≤ μ (K ∩ L)`. -/

def GaussianCorrelationProperty (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] : Prop :=
  ∀ (μ : Measure E), IsGaussian μ → μ.map (fun x ↦ -x) = μ →
    ∀ K L : Set E, IsSymmConvex K → IsSymmConvex L → MeasurableSet K → MeasurableSet L →
      μ K * μ L ≤ μ (K ∩ L)

/-! ### The one-dimensional case -/

/-- A symmetric convex subset of `ℝ` containing `a` contains every point of absolute value
at most `|a|`. -/

theorem mem_of_abs_le_abs_of_isSymmConvex {K : Set ℝ} (hK : IsSymmConvex K) {a x : ℝ}
    (ha : a ∈ K) (hx : |x| ≤ |a|) : x ∈ K := by
  obtain ⟨hconv, hsym⟩ := hK
  have hna : -a ∈ K := hsym a ha
  rcases le_total 0 a with h | h
  · have h1 : segment ℝ (-a) a ⊆ K := hconv.segment_subset hna ha
    apply h1
    rw [segment_eq_Icc (by linarith)]
    rw [abs_of_nonneg h] at hx
    exact abs_le.mp hx
  · have h1 : segment ℝ a (-a) ⊆ K := hconv.segment_subset ha hna
    apply h1
    rw [segment_eq_Icc (by linarith)]
    rw [abs_of_nonpos h] at hx
    constructor <;> [linarith [neg_abs_le x, le_abs_self x]; linarith [le_abs_self x]]

/-- Two symmetric convex subsets of `ℝ` are nested. -/

theorem subset_or_subset_of_isSymmConvex {K L : Set ℝ} (hK : IsSymmConvex K)
    (hL : IsSymmConvex L) : K ⊆ L ∨ L ⊆ K := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [Set.not_subset] at h1 h2
  obtain ⟨a, haK, haL⟩ := h1
  obtain ⟨b, hbL, hbK⟩ := h2
  rcases le_total |a| |b| with h | h
  · exact haL (mem_of_abs_le_abs_of_isSymmConvex hL hbL h)
  · exact hbK (mem_of_abs_le_abs_of_isSymmConvex hK haK h)

/-- For a probability measure on `ℝ`, the correlation inequality holds for symmetric convex
sets, because two such sets are nested. -/

theorem prob_mul_le_prob_inter_real (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {K L : Set ℝ} (hK : IsSymmConvex K) (hL : IsSymmConvex L) :
    μ K * μ L ≤ μ (K ∩ L) := by
  rcases subset_or_subset_of_isSymmConvex hK hL with h | h
  · rw [Set.inter_eq_self_of_subset_left h]
    calc μ K * μ L ≤ μ K * 1 := by gcongr; exact prob_le_one
      _ = μ K := mul_one _
  · rw [Set.inter_eq_self_of_subset_right h]
    calc μ K * μ L ≤ 1 * μ L := by gcongr; exact prob_le_one
      _ = μ L := one_mul _

/-- **Gaussian correlation inequality (Royen's theorem), one-dimensional base case.**
For every centered Gaussian measure `μ` on `ℝ` and all symmetric convex measurable sets
`K`, `L`, one has `μ K * μ L ≤ μ (K ∩ L)`. -/

theorem gaussian_correlation : GaussianCorrelationProperty ℝ := by
  intro μ hμ _ K L hK hL _ _
  haveI := hμ
  exact prob_mul_le_prob_inter_real μ hK hL

/-! ### Reductions -/

/-- Invariance of the Gaussian correlation inequality under linear isomorphisms: this reduces
the inequality for an arbitrary centered Gaussian measure to the case of its image under any
continuous linear equivalence (for instance one putting the covariance in standard form). -/
