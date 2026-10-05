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

import Mathlib

/-!
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex ComplexInnerProductSpace FourierTransform

noncomputable section

namespace Brockian.Weyl.FreeLaplacian2

/-! ## Essential self-adjointness -/

/-- A (densely defined) operator `T` with domain `D` inside a complex inner product space `H`
is *essentially self-adjoint* when it is densely defined, symmetric, and the ranges of
`T + i` and `T - i` are dense (the basic criterion for essential self-adjointness of a
symmetric operator). -/
def IsEssentiallySelfAdjoint {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : Submodule ℂ H) (T : D →ₗ[ℂ] H) : Prop :=
  Dense (D : Set H) ∧
  (∀ x y : D, ⟪T x, (y : H)⟫ = ⟪(x : H), T y⟫) ∧
  Dense (Set.range fun x : D => T x + Complex.I • (x : H)) ∧
  Dense (Set.range fun x : D => T x - Complex.I • (x : H))

/-! ## Conjugation by a unitary -/

section Conj

variable {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']

/-- The domain obtained by pulling back a domain `D ⊆ H'` along a unitary `U : H ≃ₗᵢ[ℂ] H'`. -/
def conjDomain (U : H ≃ₗᵢ[ℂ] H') (D : Submodule ℂ H') : Submodule ℂ H :=
  D.comap (U.toLinearEquiv : H →ₗ[ℂ] H')

/-- The operator `U⁻¹ T U`, the conjugate of `T` by the unitary `U`. -/
def conjOp (U : H ≃ₗᵢ[ℂ] H') (D : Submodule ℂ H') (T : D →ₗ[ℂ] H') :
    conjDomain U D →ₗ[ℂ] H :=
  (U.symm.toLinearEquiv : H' →ₗ[ℂ] H).comp
    (T.comp (((U.toLinearEquiv : H →ₗ[ℂ] H')).restrict (p := conjDomain U D) (q := D)
      (fun _ hx => hx)))

lemma conjOp_apply (U : H ≃ₗᵢ[ℂ] H') (D : Submodule ℂ H') (T : D →ₗ[ℂ] H')
    (x : conjDomain U D) :
    conjOp U D T x = U.symm (T ⟨U x, x.2⟩) := rfl

lemma conjOp_apply' (U : H ≃ₗᵢ[ℂ] H') (D : Submodule ℂ H') (T : D →ₗ[ℂ] H')
    (x : conjDomain U D) :
    U (conjOp U D T x) = T ⟨U x, x.2⟩ := by
  rw [conjOp_apply, U.apply_symm_apply]

lemma coe_conjDomain (U : H ≃ₗᵢ[ℂ] H') (D : Submodule ℂ H') :
    ((conjDomain U D : Submodule ℂ H) : Set H) = U ⁻¹' (D : Set H') := rfl

lemma inner_symm_left (U : H ≃ₗᵢ[ℂ] H') (a : H') (b : H) :
    ⟪U.symm a, b⟫ = ⟪a, U b⟫ := by
  rw [← U.inner_map_map (U.symm a) b, U.apply_symm_apply]

lemma inner_symm_right (U : H ≃ₗᵢ[ℂ] H') (a : H') (b : H) :
    ⟪U b, a⟫ = ⟪b, U.symm a⟫ := by
  rw [← U.inner_map_map b (U.symm a), U.apply_symm_apply]

/-- Every point of the domain `D` comes from a point of the pulled back domain. -/
lemma exists_conj_preimage (U : H ≃ₗᵢ[ℂ] H') (D : Submodule ℂ H') (y : D) :
    ∃ x : conjDomain U D, (⟨U x, x.2⟩ : D) = y := by
  have hmem : U.symm (y : H') ∈ conjDomain U D := by
    show U (U.symm (y : H')) ∈ D
    rw [U.apply_symm_apply]
    exact y.2
  exact ⟨⟨U.symm (y : H'), hmem⟩, Subtype.ext (by simp)⟩

/-- The shifted range of the conjugated operator is the `U`-preimage of the shifted range
of the original operator. -/
lemma conjOp_range_eq (U : H ≃ₗᵢ[ℂ] H') (D : Submodule ℂ H') (T : D →ₗ[ℂ] H') (c : ℂ) :
    (Set.range fun x : conjDomain U D => conjOp U D T x + c • (x : H)) =
      U ⁻¹' (Set.range fun y : D => T y + c • (y : H')) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨U x, x.2⟩, ?_⟩
    show T ⟨U x, x.2⟩ + c • ((⟨U x, x.2⟩ : D) : H') = U (conjOp U D T x + c • (x : H))
    rw [map_add, map_smul, conjOp_apply, U.apply_symm_apply]
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := exists_conj_preimage U D y
    refine ⟨x, ?_⟩
    apply U.injective
    have hUx : U (x : H) = (y : H') := congrArg Subtype.val hx
    rw [map_add, map_smul, conjOp_apply, U.apply_symm_apply, hx, hUx]
    exact hy

/-- Essential self-adjointness is preserved by conjugation by a unitary. -/
theorem IsEssentiallySelfAdjoint.conj (U : H ≃ₗᵢ[ℂ] H') (D : Submodule ℂ H')
    (T : D →ₗ[ℂ] H') (h : IsEssentiallySelfAdjoint D T) :
    IsEssentiallySelfAdjoint (conjDomain U D) (conjOp U D T) := by
  obtain ⟨hd, hsym, hp, hm⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [coe_conjDomain]
    exact hd.preimage U.toHomeomorph.isOpenMap
  · intro x y
    rw [conjOp_apply, conjOp_apply, inner_symm_left, ← inner_symm_right]
    exact hsym ⟨U x, x.2⟩ ⟨U y, y.2⟩
  · rw [conjOp_range_eq]
    exact hp.preimage U.toHomeomorph.isOpenMap
  · have : (Set.range fun x : conjDomain U D => conjOp U D T x - Complex.I • (x : H)) =
        Set.range fun x : conjDomain U D => conjOp U D T x + (-Complex.I) • (x : H) := by
      simp [sub_eq_add_neg]
    rw [this, conjOp_range_eq]
    have h2 : (Set.range fun y : D => T y - Complex.I • (y : H')) =
        Set.range fun y : D => T y + (-Complex.I) • (y : H') := by
      simp [sub_eq_add_neg]
    rw [← h2]
    exact hm.preimage U.toHomeomorph.isOpenMap

end Conj

/-! ## The multiplication operator on `L²` -/

section Mult

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The maximal domain of the operator of multiplication by the real function `m`
on `L²(μ)`. -/
def multDomain (μ : Measure α) (m : α → ℝ) : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f | MemLp (fun x => (m x : ℂ) * ⇑f x) 2 μ}
  add_mem' := by
    intro u v hu hv
    have h : (fun x => (m x : ℂ) * ⇑(u + v) x)
        =ᵐ[μ] (fun x => (m x : ℂ) * ⇑u x) + (fun x => (m x : ℂ) * ⇑v x) := by
      filter_upwards [Lp.coeFn_add u v] with x hx
      rw [hx]
      simp [mul_add]
    exact (memLp_congr_ae h).2 (hu.add hv)
  zero_mem' := by
    have h : (fun x => (m x : ℂ) * ⇑(0 : Lp ℂ 2 μ) x) =ᵐ[μ] (0 : α → ℂ) := by
      filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ)] with x hx
      rw [hx]
      simp
    exact (memLp_congr_ae h).2 MemLp.zero
  smul_mem' := by
    intro c u hu
    have h : (fun x => (m x : ℂ) * ⇑(c • u) x) =ᵐ[μ] c • (fun x => (m x : ℂ) * ⇑u x) := by
      filter_upwards [Lp.coeFn_smul c u] with x hx
      rw [hx]
      simp [Pi.smul_apply]
      ring
    exact (memLp_congr_ae h).2 (hu.const_smul c)

lemma mem_multDomain_iff {m : α → ℝ} {f : Lp ℂ 2 μ} :
    f ∈ multDomain μ m ↔ MemLp (fun x => (m x : ℂ) * ⇑f x) 2 μ := Iff.rfl

/-- Multiplication by the real function `m`, as an operator on `L²(μ)` with domain
`multDomain μ m`. -/
def multOp (μ : Measure α) (m : α → ℝ) : multDomain μ m →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := MemLp.toLp _ (mem_multDomain_iff.1 f.2)
  map_add' := by
    intro u v
    rw [Lp.ext_iff]
    filter_upwards [MemLp.coeFn_toLp (mem_multDomain_iff.1 (u + v).2),
      MemLp.coeFn_toLp (mem_multDomain_iff.1 u.2), MemLp.coeFn_toLp (mem_multDomain_iff.1 v.2),
      Lp.coeFn_add (MemLp.toLp _ (mem_multDomain_iff.1 u.2))
        (MemLp.toLp _ (mem_multDomain_iff.1 v.2)),
      Lp.coeFn_add (u : Lp ℂ 2 μ) (v : Lp ℂ 2 μ)] with x h1 h2 h3 h4 h5
    simp only [Submodule.coe_add, Pi.add_apply] at *
    rw [h1, h4, h2, h3, h5]
    ring
  map_smul' := by
    intro c u
    rw [Lp.ext_iff]
    filter_upwards [MemLp.coeFn_toLp (mem_multDomain_iff.1 (c • u).2),
      MemLp.coeFn_toLp (mem_multDomain_iff.1 u.2),
      Lp.coeFn_smul c (MemLp.toLp _ (mem_multDomain_iff.1 u.2)),
      Lp.coeFn_smul c (u : Lp ℂ 2 μ)] with x h1 h2 h3 h4
    simp only [SetLike.val_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul] at *
    rw [h1, h3, h2, h4]
    ring

lemma multOp_coeFn (m : α → ℝ) (f : multDomain μ m) :
    ⇑(multOp μ m f) =ᵐ[μ] fun x => (m x : ℂ) * ⇑(f : Lp ℂ 2 μ) x :=
  MemLp.coeFn_toLp (mem_multDomain_iff.1 f.2)

/-- The multiplication operator by a real function is symmetric. -/
lemma multOp_symmetric (m : α → ℝ) (u v : multDomain μ m) :
    ⟪multOp μ m u, (v : Lp ℂ 2 μ)⟫ = ⟪(u : Lp ℂ 2 μ), multOp μ m v⟫ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multOp_coeFn m u, multOp_coeFn m v] with x h1 h2
  rw [h1, h2, RCLike.inner_apply', RCLike.inner_apply']
  simp only [map_mul, Complex.conj_ofReal]
  ring

/-- Solving `(m + i s) f = g` pointwise: for `s ≠ 0` the function `g / (m + i s)` lies in the
maximal domain of the multiplication operator. -/
lemma exists_mem_multDomain_div (m : α → ℝ) (hm : Measurable m) (s : ℝ) (hs : s ≠ 0)
    (g : Lp ℂ 2 μ) :
    ∃ f : multDomain μ m,
      ⇑(f : Lp ℂ 2 μ) =ᵐ[μ] fun x => ⇑g x / ((m x : ℂ) + (s : ℂ) * Complex.I) := by
  set d : α → ℂ := fun x => (m x : ℂ) + (s : ℂ) * Complex.I with hd
  have hdim : ∀ x, (d x).im = s := by intro x; simp [hd]
  have hdre : ∀ x, (d x).re = m x := by intro x; simp [hd]
  have hdne : ∀ x, d x ≠ 0 := by
    intro x hx
    exact hs (by rw [← hdim x, hx, Complex.zero_im])
  have hnorm_s : ∀ x, |s| ≤ ‖d x‖ := by
    intro x; rw [← hdim x]; exact Complex.abs_im_le_norm (d x)
  have hnorm_m : ∀ x, |m x| ≤ ‖d x‖ := by
    intro x; rw [← hdre x]; exact Complex.abs_re_le_norm (d x)
  have hdmeas : Measurable d := (Complex.measurable_ofReal.comp hm).add measurable_const
  have hmeas : AEStronglyMeasurable (fun x => ⇑g x / d x) μ := by
    simp_rw [div_eq_mul_inv]
    exact (Lp.aestronglyMeasurable g).mul hdmeas.inv.aestronglyMeasurable
  have hsabs : (0 : ℝ) < |s| := abs_pos.2 hs
  have hbound1 : ∀ᵐ x ∂μ, ‖⇑g x / d x‖ ≤ ‖((|s|⁻¹ : ℝ) : ℂ) * ⇑g x‖ := by
    filter_upwards with x
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
      inv_mul_eq_div]
    gcongr
    exact hnorm_s x
  have hmem : MemLp (fun x => ⇑g x / d x) 2 μ :=
    MemLp.mono ((Lp.memLp g).const_mul (((|s|⁻¹ : ℝ) : ℂ))) hmeas hbound1
  have hbound2 : ∀ᵐ x ∂μ, ‖(m x : ℂ) * (⇑g x / d x)‖ ≤ ‖⇑g x‖ := by
    filter_upwards with x
    have h0 : (0 : ℝ) < ‖d x‖ := norm_pos_iff.2 (hdne x)
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, mul_div_assoc',
      div_le_iff₀ h0]
    calc |m x| * ‖⇑g x‖ ≤ ‖d x‖ * ‖⇑g x‖ :=
          mul_le_mul_of_nonneg_right (hnorm_m x) (norm_nonneg _)
      _ = ‖⇑g x‖ * ‖d x‖ := by ring
  have hmem2 : MemLp (fun x => (m x : ℂ) * (⇑g x / d x)) 2 μ :=
    MemLp.mono (Lp.memLp g)
      (((Complex.measurable_ofReal.comp hm).aestronglyMeasurable).mul hmeas) hbound2
  refine ⟨⟨hmem.toLp _, ?_⟩, hmem.coeFn_toLp⟩
  rw [mem_multDomain_iff]
  refine (memLp_congr_ae ?_).2 hmem2
  filter_upwards [hmem.coeFn_toLp] with x hx
  rw [hx]

/-- For `s ≠ 0` real, the operator `M + i s` maps the maximal domain **onto** `L²(μ)`. -/
lemma multOp_add_surjective (m : α → ℝ) (hm : Measurable m) (s : ℝ) (hs : s ≠ 0)
    (g : Lp ℂ 2 μ) :
    ∃ f : multDomain μ m, multOp μ m f + ((s : ℂ) * Complex.I) • (f : Lp ℂ 2 μ) = g := by
  obtain ⟨f, hf⟩ := exists_mem_multDomain_div m hm s hs g
  have hdne : ∀ x : α, (m x : ℂ) + (s : ℂ) * Complex.I ≠ 0 := by
    intro x hx
    apply hs
    have him : ((m x : ℂ) + (s : ℂ) * Complex.I).im = s := by simp
    rw [← him, hx, Complex.zero_im]
  refine ⟨f, ?_⟩
  rw [Lp.ext_iff]
  filter_upwards [Lp.coeFn_add (multOp μ m f) (((s : ℂ) * Complex.I) • (f : Lp ℂ 2 μ)),
    multOp_coeFn m f, Lp.coeFn_smul ((s : ℂ) * Complex.I) (f : Lp ℂ 2 μ), hf] with x h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, smul_eq_mul, h4]
  field_simp [hdne x]

/-- The maximal domain of a multiplication operator is dense. -/
lemma multDomain_dense (m : α → ℝ) (hm : Measurable m) :
    Dense ((multDomain μ m : Submodule ℂ (Lp ℂ 2 μ)) : Set (Lp ℂ 2 μ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro h hh
  set e : α → ℂ := fun x => (m x : ℂ) - Complex.I with he
  have heim : ∀ x, (e x).im = -1 := by intro x; simp [he]
  have hene : ∀ x, e x ≠ 0 := by
    intro x hx
    have := heim x
    rw [hx, Complex.zero_im] at this
    norm_num at this
  have henorm : ∀ x, (1 : ℝ) ≤ ‖e x‖ := by
    intro x
    have h1 : |(e x).im| ≤ ‖e x‖ := Complex.abs_im_le_norm (e x)
    rw [heim x] at h1
    simpa using h1
  have hemeas : Measurable e := (Complex.measurable_ofReal.comp hm).sub measurable_const
  have hmeas : AEStronglyMeasurable (fun x => ⇑h x / e x) μ := by
    simp_rw [div_eq_mul_inv]
    exact (Lp.aestronglyMeasurable h).mul hemeas.inv.aestronglyMeasurable
  have hu : MemLp (fun x => ⇑h x / e x) 2 μ := by
    refine MemLp.mono (Lp.memLp h) hmeas ?_
    filter_upwards with x
    rw [norm_div]
    exact div_le_self (norm_nonneg _) (henorm x)
  set u : Lp ℂ 2 μ := hu.toLp _ with hudef
  have key : ∀ g : Lp ℂ 2 μ, ⟪g, u⟫ = 0 := by
    intro g
    obtain ⟨f, hf⟩ := exists_mem_multDomain_div m hm 1 one_ne_zero g
    have h0 : ⟪(f : Lp ℂ 2 μ), h⟫ = 0 := (Submodule.mem_orthogonal _ _).1 hh _ f.2
    rw [L2.inner_def] at h0 ⊢
    rw [← h0]
    apply integral_congr_ae
    filter_upwards [hf, hu.coeFn_toLp] with x hx hy
    rw [hx, hy, RCLike.inner_apply', RCLike.inner_apply']
    have hd1 : ((m x : ℂ) + ((1 : ℝ) : ℂ) * Complex.I) = (m x : ℂ) + Complex.I := by simp
    rw [hd1, map_div₀]
    have hconj : (starRingEnd ℂ) ((m x : ℂ) + Complex.I) = e x := by
      simp [he, Complex.conj_ofReal, sub_eq_add_neg]
    rw [hconj]
    field_simp
  have hzero : u = 0 := by
    have := key u
    rwa [inner_self_eq_zero] at this
  rw [Lp.ext_iff]
  have hz : (fun x => ⇑h x / e x) =ᵐ[μ] (0 : α → ℂ) := by
    refine hu.coeFn_toLp.symm.trans ?_
    rw [← hudef, hzero]
    exact Lp.coeFn_zero ℂ 2 μ
  filter_upwards [hz, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ)] with x hx hx0
  rw [hx0]
  rcases div_eq_zero_iff.1 hx with h1 | h1
  · exact h1
  · exact absurd h1 (hene x)

/-- Multiplication by a real measurable function is essentially self-adjoint on its
maximal domain in `L²(μ)`. -/
theorem multOp_essentiallySelfAdjoint (m : α → ℝ) (hm : Measurable m) :
    IsEssentiallySelfAdjoint (multDomain μ m) (multOp μ m) := by
  refine ⟨multDomain_dense m hm, multOp_symmetric m, ?_, ?_⟩
  · have hrange : (Set.range fun x : multDomain μ m =>
        multOp μ m x + Complex.I • (x : Lp ℂ 2 μ)) = Set.univ := by
      ext g
      simp only [Set.mem_range, Set.mem_univ, iff_true]
      obtain ⟨f, hf⟩ := multOp_add_surjective m hm 1 one_ne_zero g
      exact ⟨f, by simpa using hf⟩
    rw [hrange]
    exact dense_univ
  · have hrange : (Set.range fun x : multDomain μ m =>
        multOp μ m x - Complex.I • (x : Lp ℂ 2 μ)) = Set.univ := by
      ext g
      simp only [Set.mem_range, Set.mem_univ, iff_true]
      obtain ⟨f, hf⟩ := multOp_add_surjective m hm (-1) (by norm_num) g
      refine ⟨f, ?_⟩
      rw [← hf, sub_eq_add_neg, ← neg_smul]
      norm_num
    rw [hrange]
    exact dense_univ

end Mult

/-! ## The free Laplacian -/

section FreeLaplacian

variable (E : Type*) [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Fourier multiplier of the free Laplacian `-Δ`: with the normalisation
`𝓕 f (ξ) = ∫ e^{-2πi⟪x, ξ⟫} f x`, one has `𝓕 (-Δ f) (ξ) = 4π²‖ξ‖² 𝓕 f (ξ)`. -/
def freeMultiplier (ξ : E) : ℝ := 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2

/-- The domain of the free Laplacian: the Sobolev space `H²`, described on the Fourier side
as the maximal domain of multiplication by `4π²‖ξ‖²`. -/
@[reducible] def freeLaplacianDomain : Submodule ℂ (Lp (α := E) ℂ 2) :=
  conjDomain (Lp.fourierTransformₗᵢ E ℂ) (multDomain volume (freeMultiplier E))

/-- The free Laplacian `-Δ` on `L²(E)`, defined as the Fourier multiplier operator with
symbol `4π²‖ξ‖²`, on its maximal domain. -/
def freeLaplacian : freeLaplacianDomain E →ₗ[ℂ] Lp (α := E) ℂ 2 :=
  conjOp (Lp.fourierTransformₗᵢ E ℂ) (multDomain volume (freeMultiplier E))
    (multOp volume (freeMultiplier E))

/-- On the Fourier side the free Laplacian really is multiplication by `4π²‖ξ‖²`. -/
lemma fourier_freeLaplacian (f : freeLaplacianDomain E) :
    ⇑(Lp.fourierTransformₗᵢ E ℂ (freeLaplacian E f))
      =ᵐ[volume] fun ξ => ((freeMultiplier E ξ : ℝ) : ℂ) *
        ⇑(Lp.fourierTransformₗᵢ E ℂ (f : Lp (α := E) ℂ 2)) ξ := by
  rw [freeLaplacian, conjOp_apply']
  exact multOp_coeFn _ _

/-- **The free Laplacian is essentially self-adjoint.**  Conjugating by the Fourier transform
turns `-Δ` into multiplication by the real symbol `4π²‖ξ‖²`, which is essentially
self-adjoint (indeed self-adjoint) on its maximal domain. -/
theorem freeLaplacian_essentiallySelfAdjoint_of_fourier :
    IsEssentiallySelfAdjoint (freeLaplacianDomain E) (freeLaplacian E) :=
  (multOp_essentiallySelfAdjoint (freeMultiplier E)
    (by unfold freeMultiplier; fun_prop)).conj _ _ _

end FreeLaplacian

end Brockian.Weyl.FreeLaplacian2

