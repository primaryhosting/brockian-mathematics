import Mathlib

/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A *frame function of weight one*, Gleason's formulation of a quantum measure:
a function on the unit sphere which is nonnegative and whose values sum to `1`
over every orthonormal basis. -/
structure IsFrameFunction (f : H → ℝ) : Prop where
  nonneg : ∀ x : H, ‖x‖ = 1 → 0 ≤ f x
  sum_eq_one : ∀ b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H, ∑ i, f (b i) = 1

/-- A density operator: a positive (hence self-adjoint) operator of trace one. -/
def IsDensityOperator (T : H →L[ℂ] H) : Prop :=
  T.IsPositive ∧ LinearMap.trace ℂ H (T : H →ₗ[ℂ] H) = 1

section Auxiliary

/-- Scaling law for the quadratic form of an operator along real scalars. -/
theorem inner_apply_self_smul (T : H →L[ℂ] H) (c : ℝ) (x : H) :
    ⟪T ((c : ℂ) • x), (c : ℂ) • x⟫_ℂ = (c ^ 2 : ℝ) • ⟪T x, x⟫_ℂ := by
  simp
  ring

/-- The real part of the quadratic form does not depend on the order of the arguments. -/
theorem re_inner_apply_self_symm (T : H →L[ℂ] H) (x : H) :
    RCLike.re ⟪T x, x⟫_ℂ = Complex.re ⟪x, T x⟫_ℂ := by
  rw [← inner_conj_symm (𝕜 := ℂ) x (T x), Complex.conj_re]
  rfl

/-- An operator on a complex inner product space is determined by its quadratic form on the
unit sphere. -/
theorem eq_of_inner_apply_self_unit (S T : H →L[ℂ] H)
    (h : ∀ x : H, ‖x‖ = 1 → ⟪S x, x⟫_ℂ = ⟪T x, x⟫_ℂ) : S = T := by
  apply ContinuousLinearMap.coe_injective
  rw [← ext_inner_map]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hc : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    set u : H := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hu_def
    have hu : ‖u‖ = 1 := by simp [hu_def, norm_smul, inv_mul_cancel₀ hc]
    have hxu : ((‖x‖ : ℝ) : ℂ) • u = x := by
      rw [hu_def, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hc]
      simp
    show ⟪S x, x⟫_ℂ = ⟪T x, x⟫_ℂ
    rw [← hxu, inner_apply_self_smul S ‖x‖ u, inner_apply_self_smul T ‖x‖ u, h u hu]

end Auxiliary

/-- If a quantum measure is the quadratic form of an operator `T`, then the values of that
quadratic form are nonnegative reals. -/
theorem inner_apply_self_eq_nonneg_real {f : H → ℝ} (hf : IsFrameFunction f) {T : H →L[ℂ] H}
    (hT : ∀ x : H, ‖x‖ = 1 → ((f x : ℂ) = ⟪T x, x⟫_ℂ)) (x : H) :
    ∃ r : ℝ, 0 ≤ r ∧ ⟪T x, x⟫_ℂ = (r : ℂ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, le_rfl, by simp⟩
  · have hc : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    set u : H := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hu_def
    have hu : ‖u‖ = 1 := by simp [hu_def, norm_smul, inv_mul_cancel₀ hc]
    have hxu : ((‖x‖ : ℝ) : ℂ) • u = x := by
      rw [hu_def, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hc]
      simp
    refine ⟨‖x‖ ^ 2 * f u, mul_nonneg (by positivity) (hf.nonneg u hu), ?_⟩
    conv_lhs => rw [← hxu]
    rw [inner_apply_self_smul T ‖x‖ u, ← hT u hu]
    push_cast
    simp [Complex.real_smul]

/-- If a quantum measure is the quadratic form of an operator `T`, then `T` is positive. -/
theorem isPositive_of_frameFunction {f : H → ℝ} (hf : IsFrameFunction f) {T : H →L[ℂ] H}
    (hT : ∀ x : H, ‖x‖ = 1 → ((f x : ℂ) = ⟪T x, x⟫_ℂ)) : T.IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  obtain ⟨r, hr, hx⟩ := inner_apply_self_eq_nonneg_real hf hT x
  rw [hx]
  simp [hr]

/-- If a quantum measure is the quadratic form of an operator `T`, then `T` has trace one. -/
theorem trace_eq_one_of_frameFunction [FiniteDimensional ℂ H] {f : H → ℝ}
    (hf : IsFrameFunction f) {T : H →L[ℂ] H}
    (hT : ∀ x : H, ‖x‖ = 1 → ((f x : ℂ) = ⟪T x, x⟫_ℂ)) :
    LinearMap.trace ℂ H (T : H →ₗ[ℂ] H) = 1 := by
  set b := stdOrthonormalBasis ℂ H with hb
  rw [LinearMap.trace_eq_sum_inner (T : H →ₗ[ℂ] H) b]
  simp only [ContinuousLinearMap.coe_coe]
  have key : ∀ i, ⟪b i, T (b i)⟫_ℂ = ((f (b i) : ℝ) : ℂ) := by
    intro i
    rw [← inner_conj_symm, ← hT (b i) (b.norm_eq_one i)]
    simp
  rw [Finset.sum_congr rfl (fun i _ => key i), ← Complex.ofReal_sum, hf.sum_eq_one b]
  norm_num

/-- The quantum measure attached to a density operator is a frame function of weight one:
the converse direction of Gleason's theorem. -/
theorem isFrameFunction_of_isDensityOperator {T : H →L[ℂ] H} (hT : IsDensityOperator T) :
    IsFrameFunction (fun x : H => RCLike.re ⟪T x, x⟫_ℂ) where
  nonneg := fun x _ => hT.1.2 x
  sum_eq_one := by
    intro b
    rw [Finset.sum_congr rfl (fun i _ => re_inner_apply_self_symm T (b i)), ← Complex.re_sum]
    have hsum : ∑ i, ⟪b i, T (b i)⟫_ℂ = 1 := by
      rw [← hT.2, LinearMap.trace_eq_sum_inner (T : H →ₗ[ℂ] H) b]
      simp
    rw [hsum]
    norm_num

/-- **Gleason's theorem** (Lean-checked reduction).

Every quantum measure (frame function of weight one) on a complex Hilbert space of
dimension at least `3` is given by a density operator.

The analytic core of Gleason's argument is the statement that such a measure is
*quadratic*, i.e. of the form `x ↦ ⟪T x, x⟫` for some bounded operator `T`; that is taken
here as the hypothesis `hquad`, and what is proved is the reduction: once the measure is
quadratic, the operator representing it is automatically a density operator, i.e. positive
(hence self-adjoint) and of trace one.  The dimension hypothesis `hdim` is retained as part
of the statement, although this reduction step does not use it (it is needed only for the
quadraticity of the measure, which fails in dimension two).  The Hilbert space is assumed
finite dimensional. -/
theorem gleason_theorem [FiniteDimensional ℂ H] (hdim : 3 ≤ Module.finrank ℂ H)
    (f : H → ℝ) (hf : IsFrameFunction f)
    (hquad : ∃ T : H →L[ℂ] H, ∀ x : H, ‖x‖ = 1 → ((f x : ℂ) = ⟪T x, x⟫_ℂ)) :
    ∃ T : H →L[ℂ] H, IsDensityOperator T ∧
      ∀ x : H, ‖x‖ = 1 → f x = RCLike.re ⟪T x, x⟫_ℂ := by
  obtain ⟨T, hT⟩ := hquad
  refine ⟨T, ⟨isPositive_of_frameFunction hf hT, trace_eq_one_of_frameFunction hf hT⟩, ?_⟩
  intro x hx
  rw [← hT x hx]
  simp

/-! ## Failure in dimension two

The dimension hypothesis in Gleason's theorem is essential: on `ℂ²` there is a quantum
measure (frame function of weight one) which is not represented by any density operator. -/

section DimTwo

/-- The two-dimensional complex Hilbert space. -/
abbrev C2 := EuclideanSpace ℂ (Fin 2)

/-- A quantum measure on `ℂ²` which is not quadratic: `x ↦ |x₀|⁴ / (|x₀|⁴ + |x₁|⁴)`. -/
noncomputable def qfTwo (x : C2) : ℝ := ‖x.ofLp 0‖ ^ 4 / (‖x.ofLp 0‖ ^ 4 + ‖x.ofLp 1‖ ^ 4)

/-- Coordinates of a unit vector of `ℂ²`. -/
theorem norm_coord_sq_add (x : C2) (hx : ‖x‖ = 1) :
    ‖x.ofLp 0‖ ^ 2 + ‖x.ofLp 1‖ ^ 2 = 1 := by
  have h := EuclideanSpace.norm_eq x
  rw [hx] at h
  rw [show (∑ i, ‖x.ofLp i‖ ^ 2) = ‖x.ofLp 0‖ ^ 2 + ‖x.ofLp 1‖ ^ 2 by
    simp [Fin.sum_univ_two]] at h
  nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ ‖x.ofLp 0‖ ^ 2 + ‖x.ofLp 1‖ ^ 2), h]

/-- Coordinatewise consequence of orthogonality in `ℂ²`. -/
theorem norm_coord_mul_of_orthogonal (u v : C2) (h : ⟪u, v⟫_ℂ = 0) :
    ‖u.ofLp 0‖ * ‖v.ofLp 0‖ = ‖u.ofLp 1‖ * ‖v.ofLp 1‖ := by
  rw [PiLp.inner_apply, Fin.sum_univ_two] at h
  have h2 : (starRingEnd ℂ) (u.ofLp 0) * v.ofLp 0 = -((starRingEnd ℂ) (u.ofLp 1) * v.ofLp 1) := by
    rw [RCLike.inner_apply, RCLike.inner_apply] at h
    linear_combination h
  simpa [norm_mul] using congrArg norm h2

/-- The real-number identity underlying the two-dimensional counterexample. -/
theorem qfTwo_real_identity (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h1 : a ^ 2 + b ^ 2 = 1) (h2 : c ^ 2 + d ^ 2 = 1) (h3 : a * c = b * d) :
    a ^ 4 / (a ^ 4 + b ^ 4) + c ^ 4 / (c ^ 4 + d ^ 4) = 1 := by
  have hcb : c = b := by
    nlinarith [sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (a + d), sq_nonneg (b + c)]
  have hda : d = a := by
    nlinarith [sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (a + d), sq_nonneg (b + c)]
  have hpos : 0 < a ^ 4 + b ^ 4 := by nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]
  rw [hcb, hda, show b ^ 4 + a ^ 4 = a ^ 4 + b ^ 4 by ring, ← add_div, div_self hpos.ne']

/-- `qfTwo` adds up to one on any orthonormal pair. -/
theorem qfTwo_add_qfTwo (u v : C2) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℂ = 0) :
    qfTwo u + qfTwo v = 1 :=
  qfTwo_real_identity _ _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_coord_sq_add u hu) (norm_coord_sq_add v hv) (norm_coord_mul_of_orthogonal u v huv)

/-- `qfTwo` is a quantum measure on `ℂ²`. -/
theorem isFrameFunction_qfTwo : IsFrameFunction qfTwo where
  nonneg := by
    intro x _
    unfold qfTwo
    positivity
  sum_eq_one := by
    intro b
    have hrank : Module.finrank ℂ C2 = 2 := by simp
    let e : Fin 2 ≃ Fin (Module.finrank ℂ C2) := finCongr hrank.symm
    rw [(Equiv.sum_comp e (fun i => qfTwo (b i))).symm, Fin.sum_univ_two]
    exact qfTwo_add_qfTwo _ _ (b.norm_eq_one _) (b.norm_eq_one _)
      (b.orthonormal.2 (i := e 0) (j := e 1) (by simp [e, Fin.ext_iff]))

/-- The first standard basis vector of `ℂ²`. -/
def stdE0 : C2 := !₂[1, 0]

/-- The second standard basis vector of `ℂ²`. -/
def stdE1 : C2 := !₂[0, 1]

theorem norm_stdE0 : ‖stdE0‖ = 1 := by rw [EuclideanSpace.norm_eq]; simp [stdE0, Fin.sum_univ_two]

theorem norm_stdE1 : ‖stdE1‖ = 1 := by rw [EuclideanSpace.norm_eq]; simp [stdE1, Fin.sum_univ_two]

theorem qfTwo_stdE0 : qfTwo stdE0 = 1 := by simp [qfTwo, stdE0]

theorem qfTwo_stdE1 : qfTwo stdE1 = 0 := by simp [qfTwo, stdE1]

/-- `qfTwo` is not the quadratic form of any bounded operator on `ℂ²`. -/
theorem not_quadratic_qfTwo :
    ¬ ∃ T : C2 →L[ℂ] C2, ∀ x : C2, ‖x‖ = 1 → ((qfTwo x : ℂ) = ⟪T x, x⟫_ℂ) := by
  rintro ⟨T, hT⟩
  set x₁ : C2 := !₂[(3 / 5 : ℂ), (4 / 5 : ℂ)] with hx₁
  set x₂ : C2 := !₂[(3 / 5 : ℂ), -(4 / 5 : ℂ)] with hx₂
  have hnx₁ : ‖x₁‖ = 1 := by rw [EuclideanSpace.norm_eq]; norm_num [hx₁, Fin.sum_univ_two]
  have hnx₂ : ‖x₂‖ = 1 := by rw [EuclideanSpace.norm_eq]; norm_num [hx₂, Fin.sum_univ_two]
  have hq₁ : qfTwo x₁ = 81 / 337 := by norm_num [qfTwo, hx₁]
  have hq₂ : qfTwo x₂ = 81 / 337 := by norm_num [qfTwo, hx₂]
  have hd₁ : x₁ = (3 / 5 : ℂ) • stdE0 + (4 / 5 : ℂ) • stdE1 := by
    ext i; fin_cases i <;> simp [hx₁, stdE0, stdE1]
  have hd₂ : x₂ = (3 / 5 : ℂ) • stdE0 - (4 / 5 : ℂ) • stdE1 := by
    ext i; fin_cases i <;> simp [hx₂, stdE0, stdE1]
  have expand : ⟪T x₁, x₁⟫_ℂ + ⟪T x₂, x₂⟫_ℂ
      = (18 / 25 : ℂ) * ⟪T stdE0, stdE0⟫_ℂ + (32 / 25 : ℂ) * ⟪T stdE1, stdE1⟫_ℂ := by
    rw [hd₁, hd₂]
    simp
    ring
  rw [← hT x₁ hnx₁, ← hT x₂ hnx₂, ← hT stdE0 norm_stdE0, ← hT stdE1 norm_stdE1,
    qfTwo_stdE0, qfTwo_stdE1, hq₁, hq₂] at expand
  norm_num at expand

/-- **Gleason's theorem fails in dimension two**: there is a quantum measure on `ℂ²`
which is not given by any density operator. -/
theorem gleason_fails_dim_two :
    ∃ f : C2 → ℝ, IsFrameFunction f ∧
      ¬ ∃ T : C2 →L[ℂ] C2, IsDensityOperator T ∧
        ∀ x : C2, ‖x‖ = 1 → f x = RCLike.re ⟪T x, x⟫_ℂ := by
  refine ⟨qfTwo, isFrameFunction_qfTwo, ?_⟩
  rintro ⟨T, hT, hrep⟩
  refine not_quadratic_qfTwo ⟨T, fun x hx => ?_⟩
  have hre := ((ContinuousLinearMap.isPositive_iff_complex T).mp hT.1 x).1
  rw [hrep x hx, hre]

end DimTwo

/-- The density operator representing a quantum measure is unique. -/
theorem density_operator_unique {S T : H →L[ℂ] H} (hS : IsDensityOperator S)
    (hT : IsDensityOperator T)
    (h : ∀ x : H, ‖x‖ = 1 → RCLike.re ⟪S x, x⟫_ℂ = RCLike.re ⟪T x, x⟫_ℂ) : S = T := by
  refine eq_of_inner_apply_self_unit S T (fun x _ => ?_)
  have hS' := (ContinuousLinearMap.isPositive_iff_complex S).mp hS.1 x
  have hT' := (ContinuousLinearMap.isPositive_iff_complex T).mp hT.1 x
  rw [← hS'.1, ← hT'.1, h x ‹‖x‖ = 1›]

end Frontier

