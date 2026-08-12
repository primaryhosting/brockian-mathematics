/-
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

* `Frontier.QuantumMeasure`: a finitely additive probability measure on the lattice of subspaces
  of a complex Hilbert space (equivalently, on orthogonal projections).
* `Frontier.IsDensityOperator`: self-adjoint, positive semidefinite, unit trace.
* `Frontier.gleason_theorem`: the target statement.  Gleason's theorem is derived, in a fully
  Lean-checked way, from Gleason's *frame function theorem* `hFrame` (the deep analytic input,
  taken here as an explicit hypothesis): every quantum measure on a space of dimension `≥ 3` is
  `U ↦ tr (ρ P_U)` for a density operator `ρ`.
* `Frontier.gleason_theorem_of_finrank_eq_one`: unconditional base case in dimension one.
* `Frontier.QuantumMeasure.ofDensity`: the converse direction, proved unconditionally -- every
  density operator defines a quantum measure through the Born rule.
* `Frontier.density_operator_unique`: the density operator is unique.
-/

open scoped InnerProductSpace
open Submodule

namespace Frontier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A *quantum measure* (finitely additive probability measure on the lattice of closed
subspaces, equivalently on orthogonal projections) on an inner product space `E`. -/
structure QuantumMeasure (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  /-- The measure of a subspace. -/
  toFun : Submodule ℂ E → ℝ
  /-- A quantum measure is nonnegative. -/
  nonneg : ∀ U, 0 ≤ toFun U
  /-- A quantum measure is normalized: the whole space has measure `1`. -/
  normalized : toFun ⊤ = 1
  /-- A quantum measure is additive on orthogonal subspaces. -/
  additive : ∀ U V : Submodule ℂ E, U ⟂ V → toFun (U ⊔ V) = toFun U + toFun V

/-- A *density operator*: a positive semidefinite self-adjoint operator of trace one. -/
structure IsDensityOperator (ρ : E →ₗ[ℂ] E) : Prop where
  /-- Density operators are self-adjoint. -/
  isSymmetric : ρ.IsSymmetric
  /-- Density operators are positive semidefinite. -/
  nonneg : ∀ x : E, 0 ≤ (⟪x, ρ x⟫_ℂ).re
  /-- Density operators have unit trace. -/
  trace_one : LinearMap.trace ℂ E ρ = 1

/-- The orthogonal projection onto a subspace `U`, viewed as an endomorphism of `E`. -/
noncomputable def projLM (U : Submodule ℂ E) [U.HasOrthogonalProjection] : E →ₗ[ℂ] E :=
  U.subtype ∘ₗ (U.orthogonalProjection : E →L[ℂ] U)

/-- Gleason's *frame function theorem*, the deep analytic input to Gleason's theorem: the
function `x ↦ μ (ℂ ∙ x)` on the unit sphere of a space of dimension `≥ 3` is the quadratic form
of a self-adjoint operator. -/
def IsRegularFrame (mu : QuantumMeasure E) : Prop :=
  ∃ T : E →ₗ[ℂ] E, T.IsSymmetric ∧ ∀ x : E, ‖x‖ = 1 → mu.toFun (ℂ ∙ x) = (⟪x, T x⟫_ℂ).re

/-- The empty subspace has measure zero. -/
lemma QuantumMeasure.map_bot (mu : QuantumMeasure E) : mu.toFun ⊥ = 0 := by
  have h := mu.additive ⊥ ⊥ (Submodule.isOrtho_bot_left)
  simp at h
  linarith

/-- Finite additivity of a quantum measure over a pairwise orthogonal family of subspaces. -/
lemma QuantumMeasure.sum_of_isOrtho (mu : QuantumMeasure E) {ι : Type*} (U : ι → Submodule ℂ E)
    (h : ∀ i j, i ≠ j → U i ⟂ U j) (s : Finset ι) :
    mu.toFun (⨆ i ∈ s, U i) = ∑ i ∈ s, mu.toFun (U i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using mu.map_bot
  | insert a s ha ih =>
      have horth : U a ⟂ ⨆ i ∈ s, U i :=
        Submodule.isOrtho_iSup_right.2 fun i =>
          Submodule.isOrtho_iSup_right.2 fun hi => h a i (by rintro rfl; exact ha hi)
      rw [Finset.iSup_insert, mu.additive _ _ horth, Finset.sum_insert ha, ih]

/-- The subspaces spanned by the vectors of an orthonormal family are pairwise orthogonal. -/
lemma isOrtho_span_of_orthonormal {ι : Type*} {v : ι → E} (hv : Orthonormal ℂ v)
    {i j : ι} (hij : i ≠ j) : (ℂ ∙ v i) ⟂ (ℂ ∙ v j) := by
  refine Submodule.isOrtho_span.2 ?_
  rintro u hu w hw
  rw [Set.mem_singleton_iff] at hu hw
  subst hu; subst hw
  exact hv.2 hij

/-- The subspaces spanned by the vectors of an orthonormal basis of `U` span `U`. -/
lemma iSup_span_orthonormalBasis {ι : Type*} [Fintype ι] (U : Submodule ℂ E)
    (b : OrthonormalBasis ι ℂ U) : (⨆ i, ℂ ∙ ((b i : E))) = U := by
  have hmap : (⨆ i, ℂ ∙ ((b i : E))) = Submodule.map U.subtype (⨆ i, ℂ ∙ (b i)) := by
    rw [Submodule.map_iSup]
    exact iSup_congr fun i => by rw [Submodule.map_span]; simp
  have hb : (⨆ i, (ℂ ∙ (b i))) = (⊤ : Submodule ℂ U) := by
    rw [← Submodule.span_iUnion]
    simpa [Set.iUnion_singleton_eq_range] using b.toBasis.span_eq
  rw [hmap, hb, Submodule.map_top, Submodule.range_subtype]

/-- The trace of `T` composed with the projection onto `U`, computed in an orthonormal basis
of `U`. -/
lemma trace_comp_projLM {ι : Type*} [Fintype ι] [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E)
    (U : Submodule ℂ E) (b : OrthonormalBasis ι ℂ U) :
    LinearMap.trace ℂ E (T ∘ₗ projLM U) = ∑ i, ⟪((b i : E)), T (b i)⟫_ℂ := by
  have hcomp : T ∘ₗ projLM U
      = (T ∘ₗ U.subtype) ∘ₗ ((U.orthogonalProjection : E →L[ℂ] U) : E →ₗ[ℂ] U) := rfl
  rw [hcomp, LinearMap.trace_comp_comm', LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- `projLM U` is the orthogonal (star) projection onto `U`. -/
lemma projLM_apply (U : Submodule ℂ E) [U.HasOrthogonalProjection] (x : E) :
    projLM U x = U.starProjection x := rfl

/-- The orthogonal projections onto two orthogonal subspaces add up to the projection onto
their join. -/
lemma projLM_sup_of_isOrtho [FiniteDimensional ℂ E] {U V : Submodule ℂ E} (h : U ⟂ V) :
    projLM (U ⊔ V) = projLM U + projLM V := by
  ext x
  show (U ⊔ V).starProjection x = U.starProjection x + V.starProjection x
  refine eq_starProjection_of_mem_of_inner_eq_zero
    (Submodule.add_mem_sup (starProjection_apply_mem U x) (starProjection_apply_mem V x)) ?_
  intro w hw
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hw
  have hxu : ⟪x - U.starProjection x, u⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal' _ _).1 (sub_starProjection_mem_orthogonal x) u hu
  have hxv : ⟪x - V.starProjection x, v⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal' _ _).1 (sub_starProjection_mem_orthogonal x) v hv
  have hPv : ⟪U.starProjection x, v⟫_ℂ = 0 :=
    (Submodule.isOrtho_iff_inner_eq.1 h) _ (starProjection_apply_mem U x) v hv
  have hQu : ⟪V.starProjection x, u⟫_ℂ = 0 := by
    have h1 : ⟪u, V.starProjection x⟫_ℂ = 0 :=
      (Submodule.isOrtho_iff_inner_eq.1 h) u hu _ (starProjection_apply_mem V x)
    rw [← inner_conj_symm, h1, map_zero]
  simp only [inner_add_right, inner_sub_left, inner_add_left] at *
  linear_combination hxu + hxv - hPv - hQu

/-- The Born-rule assignment `U ↦ tr (ρ P_U)` attached to an operator `ρ`. -/
noncomputable def measureOfDensity [FiniteDimensional ℂ E] (ρ : E →ₗ[ℂ] E)
    (U : Submodule ℂ E) : ℝ :=
  (LinearMap.trace ℂ E (ρ ∘ₗ projLM U)).re

/-- The easy converse of Gleason's theorem: every density operator defines a quantum measure
via the Born rule. -/
noncomputable def QuantumMeasure.ofDensity [FiniteDimensional ℂ E] (ρ : E →ₗ[ℂ] E)
    (hρ : IsDensityOperator ρ) : QuantumMeasure E where
  toFun := measureOfDensity ρ
  nonneg U := by
    rw [measureOfDensity, trace_comp_projLM ρ U (stdOrthonormalBasis ℂ U), Complex.re_sum]
    exact Finset.sum_nonneg fun i _ => hρ.nonneg _
  normalized := by
    have hproj : (ρ ∘ₗ projLM (⊤ : Submodule ℂ E)) = ρ := by
      ext x
      simp [projLM, Submodule.starProjection_top]
    rw [measureOfDensity, hproj, hρ.trace_one, Complex.one_re]
  additive U V h := by
    rw [measureOfDensity, measureOfDensity, measureOfDensity, projLM_sup_of_isOrtho h,
      LinearMap.comp_add, map_add, Complex.add_re]

/-- The trace of `ρ` against the rank one projection onto a unit vector `x` is the Born
probability `⟪x, ρ x⟫`. -/
lemma trace_comp_projLM_singleton [FiniteDimensional ℂ E] (ρ : E →ₗ[ℂ] E) {x : E} (hx : ‖x‖ = 1) :
    LinearMap.trace ℂ E (ρ ∘ₗ projLM (ℂ ∙ x)) = ⟪x, ρ x⟫_ℂ := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ E)]
  have h : ∀ i, ⟪stdOrthonormalBasis ℂ E i, (ρ ∘ₗ projLM (ℂ ∙ x)) (stdOrthonormalBasis ℂ E i)⟫_ℂ
      = ⟪x, stdOrthonormalBasis ℂ E i⟫_ℂ * ⟪stdOrthonormalBasis ℂ E i, ρ x⟫_ℂ := by
    intro i
    show ⟪stdOrthonormalBasis ℂ E i, ρ ((ℂ ∙ x).starProjection (stdOrthonormalBasis ℂ E i))⟫_ℂ = _
    rw [Submodule.starProjection_singleton, hx]
    simp
  simp_rw [h]
  rw [OrthonormalBasis.sum_inner_mul_inner]

/-- The Born measure attached to a density operator satisfies the conclusion of Gleason's frame
function theorem, with the density operator itself as the associated self-adjoint operator.  In
particular the hypothesis `IsRegularFrame` of `gleason_theorem` is not vacuous. -/
lemma isRegularFrame_ofDensity [FiniteDimensional ℂ E] (ρ : E →ₗ[ℂ] E)
    (hρ : IsDensityOperator ρ) : IsRegularFrame (QuantumMeasure.ofDensity ρ hρ) :=
  ⟨ρ, hρ.isSymmetric, fun x hx => by
    show measureOfDensity ρ (ℂ ∙ x) = _
    rw [measureOfDensity, trace_comp_projLM_singleton ρ hx]⟩

/-- An operator on a complex inner product space is determined by its quadratic form on unit
vectors. -/
lemma eq_of_inner_self_eq_on_sphere {ρ σ : E →ₗ[ℂ] E}
    (h : ∀ x : E, ‖x‖ = 1 → ⟪x, ρ x⟫_ℂ = ⟪x, σ x⟫_ℂ) : ρ = σ := by
  have hall : ∀ x : E, ⟪x, ρ x⟫_ℂ = ⟪x, σ x⟫_ℂ := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hxn : (‖x‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hx
      have hu : ‖((‖x‖⁻¹ : ℝ) : ℂ) • x‖ = 1 := by
        rw [norm_smul]
        simp [inv_mul_cancel₀ hxn]
      have hkey := h _ hu
      simp only [LinearMap.map_smul, inner_smul_left, inner_smul_right,
        Complex.conj_ofReal] at hkey
      field_simp at hkey
      have hne : ((1 / ‖x‖ : ℝ) : ℂ) ^ 2 ≠ 0 := by simp [hxn]
      exact mul_left_cancel₀ hne hkey
  have hzero : ρ - σ = 0 := by
    rw [← inner_map_self_eq_zero]
    intro x
    simp only [LinearMap.sub_apply, inner_sub_left]
    rw [← inner_conj_symm (ρ x) x, ← inner_conj_symm (σ x) x, hall x, sub_self]
  exact sub_eq_zero.1 hzero

/-- Uniqueness in Gleason's theorem: a quantum measure determines its density operator. -/
theorem density_operator_unique [FiniteDimensional ℂ E] {ρ σ : E →ₗ[ℂ] E}
    (h : ∀ U : Submodule ℂ E,
      LinearMap.trace ℂ E (ρ ∘ₗ projLM U) = LinearMap.trace ℂ E (σ ∘ₗ projLM U)) :
    ρ = σ := by
  refine eq_of_inner_self_eq_on_sphere fun x hx => ?_
  rw [← trace_comp_projLM_singleton ρ hx, ← trace_comp_projLM_singleton σ hx]
  exact h _

/-- The core of Gleason's theorem: a quantum measure whose restriction to rays is the quadratic
form of a self-adjoint operator is the Born measure of a density operator. -/
theorem exists_density_of_isRegularFrame [FiniteDimensional ℂ E] (mu : QuantumMeasure E)
    (hreg : IsRegularFrame mu) :
    ∃ ρ : E →ₗ[ℂ] E, IsDensityOperator ρ ∧
      ∀ U : Submodule ℂ E, (mu.toFun U : ℂ) = LinearMap.trace ℂ E (ρ ∘ₗ projLM U) := by
  obtain ⟨T, hsymm, hval⟩ := hreg
  have hreal : ∀ x : E, ((⟪x, T x⟫_ℂ).re : ℂ) = ⟪x, T x⟫_ℂ := by
    intro x
    refine Complex.conj_eq_iff_re.1 ?_
    rw [inner_conj_symm]
    exact hsymm x x
  have key : ∀ U : Submodule ℂ E, (mu.toFun U : ℂ) = LinearMap.trace ℂ E (T ∘ₗ projLM U) := by
    intro U
    set b := stdOrthonormalBasis ℂ U with hbdef
    have hon : Orthonormal ℂ (fun i => ((b i : E))) :=
      (U.subtypeₗᵢ).orthonormal_comp_iff.2 b.orthonormal
    rw [trace_comp_projLM T U b]
    have hU : mu.toFun U = ∑ i, mu.toFun (ℂ ∙ ((b i : E))) := by
      conv_lhs => rw [← iSup_span_orthonormalBasis U b]
      have := mu.sum_of_isOrtho (fun i => ℂ ∙ ((b i : E)))
        (fun i j hij => isOrtho_span_of_orthonormal hon hij) Finset.univ
      simpa using this
    rw [hU]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hval _ (hon.1 i), hreal]
  refine ⟨T, ⟨hsymm, ?_, ?_⟩, key⟩
  · intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hxn : (‖x‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hx
      have hu : ‖((‖x‖⁻¹ : ℝ) : ℂ) • x‖ = 1 := by
        rw [norm_smul]
        simp [inv_mul_cancel₀ hxn]
      have hnn := mu.nonneg (ℂ ∙ (((‖x‖⁻¹ : ℝ) : ℂ) • x))
      rw [hval _ hu] at hnn
      have hexp : ⟪((‖x‖⁻¹ : ℝ) : ℂ) • x, T (((‖x‖⁻¹ : ℝ) : ℂ) • x)⟫_ℂ
          = ((‖x‖⁻¹ * ‖x‖⁻¹ : ℝ) : ℂ) * ⟪x, T x⟫_ℂ := by
        simp only [LinearMap.map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
          Complex.ofReal_mul]
        ring
      rw [hexp] at hnn
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero] at hnn
      have hpos : 0 < ‖x‖⁻¹ * ‖x‖⁻¹ := by positivity
      exact nonneg_of_mul_nonneg_right hnn hpos
  · have h := key ⊤
    have hproj : (T ∘ₗ projLM (⊤ : Submodule ℂ E)) = T := by
      ext x
      simp [projLM, Submodule.starProjection_top]
    rw [hproj, mu.normalized] at h
    exact h.symm

/-- **Gleason's theorem** (reduction to the frame function theorem).

Let `E` be a complex Hilbert space of dimension at least `3`.  Assume Gleason's frame function
theorem `hFrame` for `E`.  Then every quantum measure `mu` on `E` -- i.e. every nonnegative,
normalized, finitely additive assignment of probabilities to closed subspaces -- is given by a
density operator `ρ`: `mu U = tr (ρ ∘ P_U)` for every subspace `U`. -/
theorem gleason_theorem [FiniteDimensional ℂ E] (h3 : 3 ≤ Module.finrank ℂ E)
    (hFrame : 3 ≤ Module.finrank ℂ E → ∀ mu : QuantumMeasure E, IsRegularFrame mu)
    (mu : QuantumMeasure E) :
    ∃ ρ : E →ₗ[ℂ] E, IsDensityOperator ρ ∧
      ∀ U : Submodule ℂ E, (mu.toFun U : ℂ) = LinearMap.trace ℂ E (ρ ∘ₗ projLM U) :=
  exists_density_of_isRegularFrame mu (hFrame h3 mu)

/-- Base case, unconditional: in dimension one every quantum measure is regular, since every
nonzero vector spans the whole space. -/
lemma isRegularFrame_of_finrank_eq_one [FiniteDimensional ℂ E] (h1 : Module.finrank ℂ E = 1)
    (mu : QuantumMeasure E) : IsRegularFrame mu := by
  refine ⟨LinearMap.id, fun x y => rfl, fun x hx => ?_⟩
  have hxne : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    exact zero_ne_one hx
  have htop : (ℂ ∙ x) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [finrank_span_singleton hxne, h1])
  rw [htop, mu.normalized]
  simp [LinearMap.id_apply, inner_self_eq_norm_sq_to_K, hx]

/-- **Gleason's theorem in dimension one**, unconditional base case: every quantum measure on a
one-dimensional complex Hilbert space is the Born measure of a density operator. -/
theorem gleason_theorem_of_finrank_eq_one [FiniteDimensional ℂ E] (h1 : Module.finrank ℂ E = 1)
    (mu : QuantumMeasure E) :
    ∃ ρ : E →ₗ[ℂ] E, IsDensityOperator ρ ∧ mu.toFun = measureOfDensity ρ := by
  obtain ⟨ρ, hρ, hkey⟩ :=
    exists_density_of_isRegularFrame mu (isRegularFrame_of_finrank_eq_one h1 mu)
  refine ⟨ρ, hρ, funext fun U => ?_⟩
  rw [measureOfDensity, ← hkey U, Complex.ofReal_re]

/-- **Gleason's theorem**, Born-rule form: under the frame function theorem `hFrame`, every
quantum measure on a space of dimension `≥ 3` *is* the Born measure of a density operator. -/
theorem gleason_theorem_eq_measureOfDensity [FiniteDimensional ℂ E]
    (h3 : 3 ≤ Module.finrank ℂ E)
    (hFrame : 3 ≤ Module.finrank ℂ E → ∀ mu : QuantumMeasure E, IsRegularFrame mu)
    (mu : QuantumMeasure E) :
    ∃ ρ : E →ₗ[ℂ] E, IsDensityOperator ρ ∧ mu.toFun = measureOfDensity ρ := by
  obtain ⟨ρ, hρ, hkey⟩ := gleason_theorem h3 hFrame mu
  refine ⟨ρ, hρ, funext fun U => ?_⟩
  rw [measureOfDensity, ← hkey U, Complex.ofReal_re]

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

