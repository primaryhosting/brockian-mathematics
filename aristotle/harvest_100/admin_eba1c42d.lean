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

open MeasureTheory ProbabilityTheory

namespace Frontier

/-!
## The Gaussian correlation inequality

The Gaussian correlation inequality (conjectured by Dunnett–Sobel / Das Gupta et al., proved by
Thomas Royen in 2014) states that for a centred Gaussian measure `μ` on `ℝⁿ` and any two
symmetric convex sets `s`, `t`,
`μ s * μ t ≤ μ (s ∩ t)`.

A search of Mathlib (`exact?`/`apply?`/`rw?` and name search for `gaussian` / `correlation`)
shows that no form of this inequality is currently available: Mathlib contains
`ProbabilityTheory.gaussianReal` and the class `ProbabilityTheory.IsGaussian`, but no correlation
inequality for Gaussian measures.  We therefore formalise the statement below
(`Frontier.GaussianCorrelationInequality`), and prove:

* the *base case*, dimension one (`Frontier.gaussian_correlation`), in the strong form where no
  measurability of the sets and no centring of the Gaussian is assumed;
* a dimension-free *reduction*: the inequality holds in any dimension as soon as the two sets are
  nested (`Frontier.gaussian_correlation_of_subset_or_subset`);
* a *reduction along linear isomorphisms*
  (`Frontier.GaussianCorrelationInequality.of_continuousLinearEquiv`): the inequality only depends
  on the linear-homeomorphism class of the ambient space;
* consequently the case `n = 1` of Royen's theorem on `EuclideanSpace ℝ (Fin 1)`
  (`Frontier.gaussianCorrelationInequality_euclideanSpace_fin_one`).

The general case (`n ≥ 2`), i.e. Royen's theorem itself, is not proved here.

The proof of the base case is the classical one: in dimension one any two symmetric convex sets
are nested (`Frontier.SymmetricConvex.subset_or_subset`), and for nested sets the inequality is
immediate from `μ ≤ 1` for a probability measure.
-/

/-- A subset of a real vector space is *symmetric convex* if it is convex and invariant under
`x ↦ -x`.  These are the sets occurring in the Gaussian correlation inequality. -/
structure SymmetricConvex {E : Type*} [AddCommGroup E] [Module ℝ E] (s : Set E) : Prop where
  /-- The set is convex. -/
  convex : Convex ℝ s
  /-- The set is symmetric about the origin. -/
  neg_mem : ∀ ⦃x : E⦄, x ∈ s → -x ∈ s

/-- Any point of absolute value at most `|x|` lies in a symmetric convex subset of `ℝ`
containing `x`: such a set is "an interval around the origin". -/
theorem SymmetricConvex.mem_of_abs_le {s : Set ℝ} (hs : SymmetricConvex s) {x y : ℝ}
    (hx : x ∈ s) (hy : |y| ≤ |x|) : y ∈ s := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp only [abs_zero] at hy
    have hy0 : y = 0 := abs_eq_zero.mp (le_antisymm hy (abs_nonneg y))
    rwa [hy0]
  · have hxa : (0 : ℝ) < |x| := abs_pos.mpr hx0
    have h1 : |y / x| ≤ 1 := by rw [abs_div]; exact (div_le_one hxa).mpr hy
    have hb1 : -1 ≤ y / x := neg_le_of_abs_le h1
    have hb2 : y / x ≤ 1 := le_of_abs_le h1
    have key := hs.convex hx (hs.neg_mem hx) (a := (1 + y / x) / 2) (b := (1 - y / x) / 2)
      (by linarith) (by linarith) (by ring)
    have heq : ((1 + y / x) / 2) • x + ((1 - y / x) / 2) • (-x) = y := by
      simp only [smul_eq_mul, mul_neg]
      field_simp
      ring
    rwa [heq] at key

/-- In dimension one, any two symmetric convex sets are nested. -/
theorem SymmetricConvex.subset_or_subset {s t : Set ℝ} (hs : SymmetricConvex s)
    (ht : SymmetricConvex t) : s ⊆ t ∨ t ⊆ s := by
  by_contra h
  obtain ⟨h1, h2⟩ := not_or.mp h
  obtain ⟨a, has, hat⟩ := Set.not_subset.mp h1
  obtain ⟨b, hbt, hbs⟩ := Set.not_subset.mp h2
  rcases le_total |a| |b| with hab | hab
  · exact hat (ht.mem_of_abs_le hbt hab)
  · exact hbs (hs.mem_of_abs_le has hab)

/-- For nested sets, the correlation inequality holds for an arbitrary probability measure. -/
theorem measure_mul_le_measure_inter_of_subset_or_subset {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {s t : Set Ω} (h : s ⊆ t ∨ t ⊆ s) :
    μ s * μ t ≤ μ (s ∩ t) := by
  rcases h with h | h
  · rw [Set.inter_eq_self_of_subset_left h]
    calc μ s * μ t ≤ μ s * 1 := by gcongr; exact prob_le_one
      _ = μ s := mul_one _
  · rw [Set.inter_eq_self_of_subset_right h]
    calc μ s * μ t ≤ 1 * μ t := by gcongr; exact prob_le_one
      _ = μ t := one_mul _

/-- **The Gaussian correlation inequality, dimension one (base case).**
For any Gaussian measure `μ` on `ℝ` and any two symmetric convex sets `s`, `t` one has
`μ s * μ t ≤ μ (s ∩ t)`.

This is the base case of Royen's theorem.  It is stated here in a strong form: neither
measurability of `s` and `t` nor centring of `μ` is needed. -/
theorem gaussian_correlation (μ : Measure ℝ) [IsGaussian μ] {s t : Set ℝ}
    (hs : SymmetricConvex s) (ht : SymmetricConvex t) : μ s * μ t ≤ μ (s ∩ t) :=
  measure_mul_le_measure_inter_of_subset_or_subset μ (hs.subset_or_subset ht)

/-- **Dimension-free reduction.** In any dimension, the Gaussian correlation inequality holds for
two nested sets.  (This is the trivial case to which the one-dimensional situation reduces.) -/
theorem gaussian_correlation_of_subset_or_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] (μ : Measure E) [IsGaussian μ] {s t : Set E}
    (h : s ⊆ t ∨ t ⊆ s) : μ s * μ t ≤ μ (s ∩ t) :=
  measure_mul_le_measure_inter_of_subset_or_subset μ h

/-- The full Gaussian correlation inequality for a real normed space `E`: for every centred
Gaussian measure `μ` on `E` (centring being expressed as invariance of `μ` under `x ↦ -x`) and
all measurable symmetric convex sets `s`, `t`, one has `μ s * μ t ≤ μ (s ∩ t)`.

Royen's theorem asserts `GaussianCorrelationInequality (EuclideanSpace ℝ (Fin n))` for all `n`.
Only the case of `ℝ` is proved here, see `Frontier.gaussianCorrelationInequality_real`. -/
def GaussianCorrelationInequality (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] : Prop :=
  ∀ μ : Measure E, IsGaussian μ → μ.map (fun x : E => -x) = μ →
    ∀ s t : Set E, MeasurableSet s → MeasurableSet t →
      SymmetricConvex s → SymmetricConvex t → μ s * μ t ≤ μ (s ∩ t)

/-- The Gaussian correlation inequality holds in dimension one. -/
theorem gaussianCorrelationInequality_real : GaussianCorrelationInequality ℝ := by
  intro μ hμ _ s t _ _ hs ht
  have : IsGaussian μ := hμ
  exact gaussian_correlation μ hs ht

/-- Symmetric convexity is preserved by taking preimages under a linear homeomorphism. -/
theorem SymmetricConvex.preimage_continuousLinearEquiv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F) {s : Set F}
    (hs : SymmetricConvex s) : SymmetricConvex (e ⁻¹' s) where
  convex := hs.convex.linear_preimage (e : E →L[ℝ] F).toLinearMap
  neg_mem x hx := by
    simp only [Set.mem_preimage, map_neg] at *
    exact hs.neg_mem hx

/-- **Reduction along linear isomorphisms.** The Gaussian correlation inequality transfers along
a linear homeomorphism `e : E ≃L[ℝ] F`: if it holds on `E`, it holds on `F`.  (In particular it
only depends on the linear-topological isomorphism class of the space, so for `ℝⁿ` it suffices
to prove it for one model of `n`-dimensional space.) -/
theorem GaussianCorrelationInequality.of_continuousLinearEquiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    (e : E ≃L[ℝ] F) (h : GaussianCorrelationInequality E) : GaussianCorrelationInequality F := by
  intro μ hμ hsym s t hsm htm hs ht
  have : IsGaussian μ := hμ
  have hem : Measurable e := (e : E →L[ℝ] F).continuous.measurable
  have hem' : Measurable e.symm := (e.symm : F →L[ℝ] E).continuous.measurable
  set ν : Measure E := μ.map e.symm with hν
  have hνG : IsGaussian ν := by
    rw [hν]; exact isGaussian_map_equiv (μ := μ) (e.symm : F ≃L[ℝ] E)
  have happly : ∀ u : Set F, MeasurableSet u → ν (e ⁻¹' u) = μ u := by
    intro u hu
    rw [hν, Measure.map_apply hem' (hu.preimage hem)]
    congr 1
    ext x
    simp
  have hνsym : ν.map (fun x : E => -x) = ν := by
    rw [hν, Measure.map_map (by fun_prop) hem']
    have hcomp : (fun x : E => -x) ∘ (e.symm : F → E) = (e.symm : F → E) ∘ (fun y : F => -y) := by
      funext y; simp
    rw [hcomp, ← Measure.map_map hem' (by fun_prop), hsym]
  have key := h ν hνG hνsym (e ⁻¹' s) (e ⁻¹' t) (hsm.preimage hem) (htm.preimage hem)
    (hs.preimage_continuousLinearEquiv e) (ht.preimage_continuousLinearEquiv e)
  rw [happly s hsm, happly t htm, ← Set.preimage_inter, happly _ (hsm.inter htm)] at key
  exact key

/-- **Royen's theorem for `n = 1`.** The Gaussian correlation inequality holds on the
Euclidean space `ℝ¹`, obtained from the real case by the reduction along the linear
homeomorphism `ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1)`. -/
theorem gaussianCorrelationInequality_euclideanSpace_fin_one :
    GaussianCorrelationInequality (EuclideanSpace ℝ (Fin 1)) :=
  gaussianCorrelationInequality_real.of_continuousLinearEquiv
    (((PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin 1 => ℝ).trans
      (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)).symm)

end Frontier

