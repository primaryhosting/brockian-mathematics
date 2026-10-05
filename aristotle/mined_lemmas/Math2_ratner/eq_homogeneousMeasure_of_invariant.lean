import Mathlib

/-!
# Ratner
Category: Frontier Math
Target: Math2.ratner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real Nat Classical Pointwise

open MeasureTheory Topology Filter Set

namespace Math2

noncomputable section

/-! ## Setting

We work with the homogeneous space `X = G / Γ` where `G = ℝ²` is an abelian Lie group and
`Γ = ℤ²` is a lattice in it, so that `X` is the two–dimensional torus `𝕋² = ℝ²/ℤ²`.
Since `G` is abelian, every one–parameter subgroup `t ↦ t • v` of `G` is unipotent
(the adjoint representation is trivial), so the flow it induces on `X` is a unipotent flow.

This is the classical abelian model case of Ratner's theorems, containing the linear flows on
the torus with irrational slope. -/

/-- The two-dimensional torus `ℝ²/ℤ²`, the homogeneous space `G/Γ` for `G = ℝ²`, `Γ = ℤ²`. -/
abbrev Torus : Type := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

/-- The projection `ℝ² → ℝ²/ℤ²`. -/

lemma eq_homogeneousMeasure_of_invariant (v : ℝ × ℝ) (x : Torus) (μ : Measure Torus)
    [IsProbabilityMeasure μ] (hinv : ∀ h ∈ H v, Measure.map (· + h) μ = μ)
    (hsupp : μ ((fun h => x + h) '' (H v : Set Torus)) = 1) :
    μ = homogeneousMeasure v x := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  set F : Torus → ℝ := fun y => ∫ h : ↑(H v), f (y + (h : Torus)) ∂(haarH v) with hFdef
  have hint : Integrable
      (Function.uncurry fun (y : Torus) (h : ↑(H v)) => f (y + (h : Torus)))
      (μ.prod (haarH v)) := by
    refine Integrable.mono' (integrable_const ‖f‖) ?_
      (Filter.Eventually.of_forall fun z => f.norm_coe_le_norm _)
    exact (f.continuous.comp
      (continuous_fst.add (continuous_subtype_val.comp continuous_snd))).aestronglyMeasurable
  -- averaging the invariance of `μ` over `H`
  have hinner : ∀ h : ↑(H v), (∫ y, f (y + (h : Torus)) ∂μ) = ∫ y, f y ∂μ := by
    intro h
    have hmeas : Measurable (fun y : Torus => y + (h : Torus)) := measurable_add_const _
    have h1 := hinv (h : Torus) h.2
    have h2 : ∫ y, f y ∂(Measure.map (fun y : Torus => y + (h : Torus)) μ) = ∫ y, f y ∂μ := by
      rw [h1]
    rwa [integral_map hmeas.aemeasurable f.continuous.aestronglyMeasurable] at h2
  have hswap : (∫ y, F y ∂μ) = ∫ y, f y ∂μ := by
    rw [hFdef]
    rw [integral_integral_swap hint]
    simp only [hinner]
    rw [integral_const, measure_univ, ENNReal.toReal_one, one_smul]
  -- `F` is constant along the coset `x + H v`
  have hcoset : ∀ y ∈ (fun h => x + h) '' (H v : Set Torus), F y = F x := by
    rintro - ⟨h₀, hh₀, rfl⟩
    have := integral_add_left_eq_self (μ := haarH v)
      (fun h : ↑(H v) => f (x + (h : Torus))) (⟨h₀, hh₀⟩ : ↑(H v))
    simpa [hFdef, add_assoc] using this
  have hae : F =ᵐ[μ] fun _ => F x := by
    have hnull : μ (((fun h => x + h) '' (H v : Set Torus))ᶜ) = 0 := by
      rw [measure_compl (isClosed_coset v x).measurableSet (measure_ne_top μ _), hsupp,
        measure_univ, tsub_self]
    filter_upwards [measure_zero_iff_ae_notMem.mp hnull] with y hy
    exact hcoset y (by simpa using hy)
  have hFint : (∫ y, F y ∂μ) = F x := by
    rw [integral_congr_ae hae, integral_const, measure_univ, ENNReal.toReal_one, one_smul]
  rw [← hswap, hFint, integral_homogeneousMeasure]

/-! ## The main statement -/

/-- **Ratner's theorems for unipotent flows**, in the abelian model case
`G = ℝ²`, `Γ = ℤ²`, `X = G/Γ = 𝕋²`, with the unipotent one-parameter subgroup
`u_t = t • v`.

There is a closed connected subgroup `H ≤ X` containing the whole orbit of the identity under
the flow such that:

* (orbit closure theorem) every orbit closure `cl {u_t · x}` is the homogeneous coset `x + H`;
* (measure classification) a Borel probability measure on `X` is invariant under the unipotent
  flow if and only if it is invariant under the (larger) group `H`, i.e. every invariant measure
  is homogeneous along `H`.
-/
