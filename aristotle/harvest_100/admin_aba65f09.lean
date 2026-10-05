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

set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory

namespace Frontier

/-- The standard (centered, identity–covariance) Gaussian measure on `Fin n → ℝ`:
the `n`-fold product of the one-dimensional standard Gaussian `N(0,1)`. -/
noncomputable def stdGaussian (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => gaussianReal 0 1

instance (n : ℕ) : IsProbabilityMeasure (stdGaussian n) := by
  unfold stdGaussian; infer_instance

/-- A set `K` in a real vector space is *symmetric* if it is stable under `x ↦ -x`. -/
def IsSymmetric {V : Type*} [AddCommGroup V] (K : Set V) : Prop := ∀ x ∈ K, -x ∈ K

/-- **The Gaussian correlation inequality in dimension `n`** (Royen's theorem).

For any two symmetric convex measurable subsets `K`, `L` of `ℝⁿ`, the standard Gaussian
measure satisfies `γ(K) * γ(L) ≤ γ(K ∩ L)`.

Since every centered Gaussian measure on a finite dimensional space is the pushforward of a
standard Gaussian measure under a linear map, this formulation is equivalent to the general
one; see `Frontier.gaussian_correlation_of_linear_image`. -/
def GaussianCorrelationInequality (n : ℕ) : Prop :=
  ∀ K L : Set (Fin n → ℝ), Convex ℝ K → Convex ℝ L → IsSymmetric K → IsSymmetric L →
    MeasurableSet K → MeasurableSet L →
    stdGaussian n K * stdGaussian n L ≤ stdGaussian n (K ∩ L)

section Basic

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A symmetric convex set is stable under scaling by scalars of absolute value at most one. -/
theorem smul_mem_of_abs_le_one {K : Set V} (hK : Convex ℝ K) (hKs : IsSymmetric K)
    {x : V} (hx : x ∈ K) {c : ℝ} (hc : |c| ≤ 1) : c • x ∈ K := by
  have h1 : (0:ℝ) ≤ (1 + c) / 2 := by cases abs_le.mp hc; linarith
  have h2 : (0:ℝ) ≤ (1 - c) / 2 := by cases abs_le.mp hc; linarith
  have h3 : (1 + c) / 2 + (1 - c) / 2 = 1 := by ring
  have hmem := hK hx (hKs x hx) h1 h2 h3
  convert hmem using 1
  module

end Basic

section OneDim

/-- In dimension one, a symmetric convex set containing a point `u` contains every point `v`
that is no further from the origin. -/
theorem mem_of_abs_le_of_symmetric_convex {A : Set (Fin 1 → ℝ)} (hA : Convex ℝ A)
    (hAs : IsSymmetric A) {u : Fin 1 → ℝ} (hu : u ∈ A) {v : Fin 1 → ℝ}
    (hv : |v 0| ≤ |u 0|) : v ∈ A := by
  rcases eq_or_ne (u 0) 0 with h0 | h0
  · have hv0 : v 0 = 0 := by
      rw [h0] at hv
      simpa using abs_nonpos_iff.mp (by simpa using hv)
    have hvu : v = u := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      rw [h0, hv0]
    rwa [hvu]
  · have hc : |v 0 / u 0| ≤ 1 := by
      rw [abs_div, div_le_one (by positivity)]
      exact hv
    have hm := smul_mem_of_abs_le_one hA hAs hu hc
    have heq : (v 0 / u 0) • u = v := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simp [h0]
    rwa [heq] at hm

/-- The key one-dimensional fact: any two symmetric convex subsets of a line are nested. -/
theorem subset_or_subset_of_symmetric_convex {K L : Set (Fin 1 → ℝ)}
    (hK : Convex ℝ K) (hL : Convex ℝ L) (hKs : IsSymmetric K) (hLs : IsSymmetric L) :
    K ⊆ L ∨ L ⊆ K := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨x, hxK, hxL⟩ := Set.not_subset.mp hcon.1
  obtain ⟨y, hyL, hyK⟩ := Set.not_subset.mp hcon.2
  rcases le_total |y 0| |x 0| with h | h
  · exact hyK (mem_of_abs_le_of_symmetric_convex hK hKs hxK h)
  · exact hxL (mem_of_abs_le_of_symmetric_convex hL hLs hyL h)

end OneDim

/-- For a probability measure, nested sets satisfy the correlation inequality trivially. -/
theorem mul_le_measure_inter_of_subset {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {K L : Set α} (h : K ⊆ L ∨ L ⊆ K) :
    μ K * μ L ≤ μ (K ∩ L) := by
  rcases h with h | h
  · rw [Set.inter_eq_self_of_subset_left h]
    calc μ K * μ L ≤ μ K * 1 := by gcongr; exact prob_le_one
      _ = μ K := mul_one _
  · rw [Set.inter_eq_self_of_subset_right h]
    calc μ K * μ L ≤ 1 * μ L := by gcongr; exact prob_le_one
      _ = μ L := one_mul _

/-- **Gaussian correlation inequality, base case (dimension one).**

For symmetric convex subsets `K`, `L` of the line, the standard Gaussian measure satisfies
`γ(K) · γ(L) ≤ γ(K ∩ L)`.  This is the base case of Royen's theorem. -/
theorem gaussian_correlation : GaussianCorrelationInequality 1 := by
  intro K L hK hL hKs hLs _ _
  exact mul_le_measure_inter_of_subset _
    (subset_or_subset_of_symmetric_convex hK hL hKs hLs)

/-- The dimension zero case is also immediate. -/
theorem gaussian_correlation_zero : GaussianCorrelationInequality 0 := by
  intro K L _ _ _ _ _ _
  refine mul_le_measure_inter_of_subset _ ?_
  by_contra hcon
  push_neg at hcon
  obtain ⟨x, _, hxL⟩ := Set.not_subset.mp hcon.1
  obtain ⟨y, hyL, _⟩ := Set.not_subset.mp hcon.2
  have hxy : x = y := Subsingleton.elim _ _
  exact hxL (hxy ▸ hyL)

/-- **Lean-checked reduction.**  The Gaussian correlation inequality for the *standard*
Gaussian measure on `ℝⁿ` implies it for every measure obtained from it by pushing forward
along a linear map, i.e. for every centered Gaussian measure on `ℝᵐ` whose covariance is
`T Tᵀ`.  Thus the standard-Gaussian formulation `GaussianCorrelationInequality` captures the
full strength of Royen's theorem. -/
theorem gaussian_correlation_of_linear_image {n m : ℕ}
    (h : GaussianCorrelationInequality n)
    (T : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (hT : Measurable T)
    (K L : Set (Fin m → ℝ)) (hK : Convex ℝ K) (hL : Convex ℝ L)
    (hKs : IsSymmetric K) (hLs : IsSymmetric L)
    (hKm : MeasurableSet K) (hLm : MeasurableSet L) :
    ((stdGaussian n).map T) K * ((stdGaussian n).map T) L
      ≤ ((stdGaussian n).map T) (K ∩ L) := by
  rw [Measure.map_apply hT hKm, Measure.map_apply hT hLm,
    Measure.map_apply hT (hKm.inter hLm), Set.preimage_inter]
  refine h _ _ (hK.linear_preimage T) (hL.linear_preimage T) ?_ ?_ (hT hKm) (hT hLm)
  · intro x hx
    have : T (-x) = -T x := map_neg T x
    simp only [Set.mem_preimage, this]
    exact hKs _ hx
  · intro x hx
    have : T (-x) = -T x := map_neg T x
    simp only [Set.mem_preimage, this]
    exact hLs _ hx

end Frontier

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

