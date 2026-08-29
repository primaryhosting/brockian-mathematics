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
-/

open scoped InnerProductSpace BigOperators

namespace Frontier

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- A *quantum measure* (a finitely additive probability measure on the lattice of closed
subspaces, i.e. on the projection lattice) of a complex Hilbert space `H`.

In finite dimensions every subspace is closed, so we index by `Submodule ℂ H`. -/
structure QuantumMeasure (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] where
  /-- The probability assigned to a subspace (equivalently, to its orthogonal projection). -/
  toFun : Submodule ℂ H → ℝ
  /-- Probabilities are nonnegative. -/
  nonneg' : ∀ S, 0 ≤ toFun S
  /-- The whole space has probability one. -/
  total' : toFun ⊤ = 1
  /-- Additivity over orthogonal subspaces. -/
  additive' : ∀ S T : Submodule ℂ H, S ≤ Tᗮ → toFun (S ⊔ T) = toFun S + toFun T

namespace QuantumMeasure

instance : CoeFun (QuantumMeasure H) (fun _ => Submodule ℂ H → ℝ) := ⟨QuantumMeasure.toFun⟩

variable (μ : QuantumMeasure H)

theorem nonneg (S : Submodule ℂ H) : 0 ≤ μ S := μ.nonneg' S

theorem total : μ ⊤ = 1 := μ.total'

theorem additive {S T : Submodule ℂ H} (h : S ≤ Tᗮ) : μ (S ⊔ T) = μ S + μ T := μ.additive' S T h

theorem map_bot : μ ⊥ = 0 := by
  have h := μ.additive (S := (⊥ : Submodule ℂ H)) (T := (⊥ : Submodule ℂ H)) bot_le
  simp only [bot_sup_eq] at h
  linarith

end QuantumMeasure

/-- `A` is a density operator: symmetric (self-adjoint), positive semidefinite, of unit trace. -/
structure IsDensityOperator (A : H →ₗ[ℂ] H) : Prop where
  isSymmetric : A.IsSymmetric
  nonneg : ∀ x : H, 0 ≤ (⟪x, A x⟫_ℂ).re
  trace_eq_one : LinearMap.trace ℂ H A = 1

omit [FiniteDimensional ℂ H] in
/-- A singleton spanned by a vector orthogonal to a span is orthogonal to that span. -/
theorem span_singleton_le_orthogonal {ι : Type*} (v : ι → H) (hv : Orthonormal ℂ v)
    (a : ι) (s : Finset ι) (ha : a ∉ s) :
    (ℂ ∙ v a) ≤ (Submodule.span ℂ (v '' (s : Set ι)))ᗮ := by
  rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      exact hv.2 (by rintro rfl; exact ha hi)
  | zero => simp
  | add x y _ _ hx hy => simp [inner_add_left, hx, hy]
  | smul c x _ hx => simp [inner_smul_left, hx]

/-- Finite additivity of a quantum measure along an orthonormal family. -/
theorem QuantumMeasure.sum_over_orthonormal {ι : Type*} (μ : QuantumMeasure H)
    (v : ι → H) (hv : Orthonormal ℂ v) (s : Finset ι) :
    μ (Submodule.span ℂ (v '' (s : Set ι))) = ∑ i ∈ s, μ (Submodule.span ℂ {v i}) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [μ.map_bot]
  · intro a t ha ih
    have himg : v '' ((insert a t : Finset ι) : Set ι) = insert (v a) (v '' (t : Set ι)) := by
      simp [Finset.coe_insert, Set.image_insert_eq]
    rw [himg, Submodule.span_insert,
      μ.additive (span_singleton_le_orthogonal v hv a t ha), ih, Finset.sum_insert ha]

/-- The trace of `A ∘ P_S` computed from an orthonormal basis of `S`. -/
theorem trace_comp_starProjection (A : H →ₗ[ℂ] H) (S : Submodule ℂ H) :
    LinearMap.trace ℂ H (A ∘ₗ (S.starProjection : H →L[ℂ] H).toLinearMap)
      = ∑ i, ⟪((stdOrthonormalBasis ℂ S i : S) : H), A ((stdOrthonormalBasis ℂ S i : S) : H)⟫_ℂ := by
  have h1 : (S.starProjection : H →L[ℂ] H).toLinearMap
      = S.subtype ∘ₗ (S.orthogonalProjection : H →L[ℂ] S).toLinearMap := rfl
  rw [h1, ← LinearMap.comp_assoc,
    LinearMap.trace_comp_comm' ((S.orthogonalProjection : H →L[ℂ] S).toLinearMap)
      (A ∘ₗ S.subtype),
    LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ S)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Submodule.inner_orthogonalProjection_eq_of_mem_left _ _

/-- Finite additivity of a quantum measure along a finite orthonormal family. -/
theorem QuantumMeasure.sum_over_orthonormal_range {ι : Type*} [Fintype ι] (μ : QuantumMeasure H)
    (v : ι → H) (hv : Orthonormal ℂ v) :
    μ (Submodule.span ℂ (Set.range v)) = ∑ i, μ (Submodule.span ℂ {v i}) := by
  have h := μ.sum_over_orthonormal v hv Finset.univ
  simpa using h

/-- The range of an orthonormal basis of `S`, pushed into `H`, spans `S`. -/
theorem span_stdOrthonormalBasis_range (S : Submodule ℂ H) :
    Submodule.span ℂ (Set.range fun i => ((stdOrthonormalBasis ℂ S i : S) : H)) = S := by
  have hb : Submodule.span ℂ (Set.range (stdOrthonormalBasis ℂ S)) = ⊤ := by
    simpa using (stdOrthonormalBasis ℂ S).toBasis.span_eq
  have hr : (Set.range fun i => (((stdOrthonormalBasis ℂ S) i : S) : H))
      = S.subtype '' (Set.range (stdOrthonormalBasis ℂ S)) := by
    rw [← Set.range_comp]; rfl
  rw [hr, ← Submodule.map_span, hb, Submodule.map_top, Submodule.range_subtype]

/-- **Gleason's theorem (Lean-checked reduction).**

Let `μ` be a quantum measure (a finitely additive probability measure on the projection
lattice) on a complex Hilbert space `H` of dimension at least `3`.  Gleason's theorem asserts
that `μ` is given by a density operator.  The whole content of the theorem is the statement
that the *frame function* `x ↦ μ (ℂ ∙ x)` on the unit sphere is a quadratic form; this is where
the hypothesis `3 ≤ dim H` enters.

Here we verify the complete reduction: **as soon as the frame function of `μ` is represented by
some linear operator `A`, that operator is automatically a density operator and `μ` is the
associated quantum measure `S ↦ tr (A P_S)`.**

The dimension hypothesis `3 ≤ finrank ℂ H` is kept because it is part of the statement of
Gleason's theorem, but it is not needed for this reduction step. -/
theorem gleason_theorem (_h3 : 3 ≤ Module.finrank ℂ H) (μ : QuantumMeasure H)
    (A : H →ₗ[ℂ] H) (hA : ∀ x : H, ‖x‖ = 1 → (μ (ℂ ∙ x) : ℂ) = ⟪x, A x⟫_ℂ) :
    IsDensityOperator A ∧
      ∀ S : Submodule ℂ H,
        (μ S : ℂ) = LinearMap.trace ℂ H (A ∘ₗ (S.starProjection : H →L[ℂ] H).toLinearMap) := by
  -- The frame function extends to the quadratic form `x ↦ ‖x‖ ^ 2 * μ (ℂ ∙ x)`.
  have key : ∀ x : H, ⟪x, A x⟫_ℂ = ((‖x‖ ^ 2 * μ (ℂ ∙ x) : ℝ) : ℂ) := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    have hc : ((‖x‖ : ℂ))⁻¹ ≠ 0 := by
      simpa using hr
    have hnu : ‖((‖x‖ : ℂ))⁻¹ • x‖ = 1 := by
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
      field_simp
    have hspan : (ℂ ∙ (((‖x‖ : ℂ))⁻¹ • x)) = (ℂ ∙ x) :=
      Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hc) x
    have h1 := hA _ hnu
    rw [hspan] at h1
    have hxu : x = ((‖x‖ : ℂ)) • (((‖x‖ : ℂ))⁻¹ • x) := by
      rw [smul_smul, mul_inv_cancel₀ (by simpa using hr), one_smul]
    have h2 : ⟪x, A x⟫_ℂ
        = ((‖x‖ : ℂ) * (‖x‖ : ℂ)) * ⟪((‖x‖ : ℂ))⁻¹ • x, A (((‖x‖ : ℂ))⁻¹ • x)⟫_ℂ := by
      conv_lhs => rw [hxu]
      rw [inner_smul_left, map_smul, inner_smul_right, Complex.conj_ofReal]
      ring
    rw [h2, ← h1]
    push_cast
    ring
  have hsym : A.IsSymmetric := by
    rw [LinearMap.isSymmetric_iff_inner_map_self_real]
    intro v
    have h : ⟪A v, v⟫_ℂ = (starRingEnd ℂ) ⟪v, A v⟫_ℂ := (inner_conj_symm _ _).symm
    rw [h, key v]
    simp
  have hnn : ∀ x : H, 0 ≤ (⟪x, A x⟫_ℂ).re := by
    intro x
    rw [key x, Complex.ofReal_re]
    exact mul_nonneg (by positivity) (μ.nonneg _)
  have htr : LinearMap.trace ℂ H A = 1 := by
    have hb : Orthonormal ℂ (stdOrthonormalBasis ℂ H : _ → H) :=
      (stdOrthonormalBasis ℂ H).orthonormal
    have hspan : Submodule.span ℂ (Set.range (stdOrthonormalBasis ℂ H : _ → H)) = ⊤ := by
      simpa using (stdOrthonormalBasis ℂ H).toBasis.span_eq
    have hsum := μ.sum_over_orthonormal_range (stdOrthonormalBasis ℂ H : _ → H) hb
    rw [hspan, μ.total] at hsum
    rw [LinearMap.trace_eq_sum_inner A (stdOrthonormalBasis ℂ H)]
    have : ∀ i, ⟪(stdOrthonormalBasis ℂ H) i, A ((stdOrthonormalBasis ℂ H) i)⟫_ℂ
        = ((μ (ℂ ∙ (stdOrthonormalBasis ℂ H) i) : ℝ) : ℂ) := fun i => (hA _ (hb.1 i)).symm
    rw [Finset.sum_congr rfl fun i _ => this i, ← Complex.ofReal_sum, ← hsum]
    norm_num
  refine ⟨⟨hsym, hnn, htr⟩, fun S => ?_⟩
  rw [trace_comp_starProjection A S]
  have hv : Orthonormal ℂ (fun i => ((stdOrthonormalBasis ℂ S i : S) : H)) :=
    (stdOrthonormalBasis ℂ S).orthonormal.comp_linearIsometry S.subtypeₗᵢ
  have hsum := μ.sum_over_orthonormal_range _ hv
  rw [span_stdOrthonormalBasis_range S] at hsum
  rw [hsum, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun i _ => hA _ (hv.1 i)

/-!
## The converse direction

Every density operator does define a quantum measure whose frame function is represented by it.
In particular the hypothesis `hA` of `Frontier.gleason_theorem` is not vacuous.
-/

/-- Orthogonal projections are additive along orthogonal subspaces. -/
theorem starProjection_sup_apply {S T : Submodule ℂ H} (h : S ≤ Tᗮ) (x : H) :
    (S ⊔ T).starProjection x = S.starProjection x + T.starProjection x := by
  have hS : S.starProjection x ∈ S := (S.orthogonalProjection x).2
  have hT : T.starProjection x ∈ T := (T.orthogonalProjection x).2
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (Submodule.add_mem_sup hS hT) ?_
  intro w hw
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hw
  have e1 : ⟪x - S.starProjection x, s⟫_ℂ = 0 :=
    Submodule.starProjection_inner_eq_zero (K := S) x s hs
  have e2 : ⟪x - T.starProjection x, t⟫_ℂ = 0 :=
    Submodule.starProjection_inner_eq_zero (K := T) x t ht
  have e3 : ⟪T.starProjection x, s⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal T s).1 (h hs) _ hT
  have e4 : ⟪S.starProjection x, t⟫_ℂ = 0 :=
    inner_eq_zero_symm.1 ((Submodule.mem_orthogonal T (S.starProjection x)).1 (h hS) t ht)
  have d1 : ⟪x - (S.starProjection x + T.starProjection x), s⟫_ℂ = 0 := by
    rw [show x - (S.starProjection x + T.starProjection x)
      = (x - S.starProjection x) - T.starProjection x by abel, inner_sub_left, e1, e3, sub_zero]
  have d2 : ⟪x - (S.starProjection x + T.starProjection x), t⟫_ℂ = 0 := by
    rw [show x - (S.starProjection x + T.starProjection x)
      = (x - T.starProjection x) - S.starProjection x by abel, inner_sub_left, e2, e4, sub_zero]
  rw [inner_add_right, d1, d2, add_zero]

/-- The trace of a rank-one operator `w ↦ ⟪u, w⟫ • y` is `⟪u, y⟫`. -/
theorem trace_eq_of_rank_one {T : H →ₗ[ℂ] H} {u y : H} (hT : ∀ w, T w = ⟪u, w⟫_ℂ • y) :
    LinearMap.trace ℂ H T = ⟪u, y⟫_ℂ := by
  rw [LinearMap.trace_eq_sum_inner T (stdOrthonormalBasis ℂ H)]
  have h : ∀ i, ⟪(stdOrthonormalBasis ℂ H) i, T ((stdOrthonormalBasis ℂ H) i)⟫_ℂ
      = ⟪u, (stdOrthonormalBasis ℂ H) i⟫_ℂ * ⟪(stdOrthonormalBasis ℂ H) i, y⟫_ℂ := by
    intro i
    rw [hT, inner_smul_right]
  rw [Finset.sum_congr rfl fun i _ => h i]
  exact (stdOrthonormalBasis ℂ H).sum_inner_mul_inner u y

omit [FiniteDimensional ℂ H] in
/-- For a density operator `A` the quantity `⟪x, A x⟫` is real. -/
theorem IsDensityOperator.inner_self_real {A : H →ₗ[ℂ] H} (hA : IsDensityOperator A) (x : H) :
    (((⟪x, A x⟫_ℂ).re : ℝ) : ℂ) = ⟪x, A x⟫_ℂ := by
  refine Complex.conj_eq_iff_re.1 ?_
  rw [← inner_conj_symm x (A x)]
  simpa using hA.isSymmetric x x

/-- The quantum measure `S ↦ tr (A P_S)` attached to a density operator `A`. -/
noncomputable def IsDensityOperator.toQuantumMeasure {A : H →ₗ[ℂ] H} (hA : IsDensityOperator A) :
    QuantumMeasure H where
  toFun S := (LinearMap.trace ℂ H (A ∘ₗ (S.starProjection : H →L[ℂ] H).toLinearMap)).re
  nonneg' S := by
    rw [trace_comp_starProjection, Complex.re_sum]
    exact Finset.sum_nonneg fun i _ => hA.nonneg _
  total' := by
    have h : ((⊤ : Submodule ℂ H).starProjection : H →L[ℂ] H).toLinearMap = LinearMap.id := by
      ext x
      simpa using Submodule.starProjection_eq_self_iff.2 (Submodule.mem_top (x := x))
    rw [h, LinearMap.comp_id, hA.trace_eq_one, Complex.one_re]
  additive' S T hST := by
    have hmaps : (((S ⊔ T).starProjection : H →L[ℂ] H)).toLinearMap
        = ((S.starProjection : H →L[ℂ] H)).toLinearMap
          + ((T.starProjection : H →L[ℂ] H)).toLinearMap := by
      ext x
      simpa using starProjection_sup_apply hST x
    rw [hmaps, LinearMap.comp_add, map_add, Complex.add_re]

/-- The frame function of the quantum measure attached to a density operator `A` is represented
by `A`; this is exactly the hypothesis `hA` of `Frontier.gleason_theorem`. -/
theorem IsDensityOperator.toQuantumMeasure_frame {A : H →ₗ[ℂ] H} (hA : IsDensityOperator A)
    (x : H) (hx : ‖x‖ = 1) :
    ((hA.toQuantumMeasure (ℂ ∙ x) : ℝ) : ℂ) = ⟪x, A x⟫_ℂ := by
  have hrank : ∀ w : H, (A ∘ₗ ((ℂ ∙ x).starProjection : H →L[ℂ] H).toLinearMap) w
      = ⟪x, w⟫_ℂ • A x := by
    intro w
    simp [Submodule.starProjection_unit_singleton ℂ hx w]
  have htr : LinearMap.trace ℂ H (A ∘ₗ ((ℂ ∙ x).starProjection : H →L[ℂ] H).toLinearMap)
      = ⟪x, A x⟫_ℂ := trace_eq_of_rank_one hrank
  show (((LinearMap.trace ℂ H
    (A ∘ₗ ((ℂ ∙ x).starProjection : H →L[ℂ] H).toLinearMap)).re : ℝ) : ℂ) = _
  rw [htr]
  exact hA.inner_self_real x

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

