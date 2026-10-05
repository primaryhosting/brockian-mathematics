import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
Stone's theorem: the infinitesimal generator of a strongly continuous one-parameter
unitary group on a complex Hilbert space is (essentially) the self-adjoint operator
`A` with `U t = exp (t * I * A)`; here we prove that the generator, defined as an
unbounded operator (a `LinearPMap`) on its natural domain, is self-adjoint.
-/

namespace QPhys

open MeasureTheory Set Filter Topology
open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A strongly continuous one-parameter unitary group on a complex Hilbert space. -/
structure IsUnitaryGroup (U : ℝ → (H →L[ℂ] H)) : Prop where
  /-- `U 0` is the identity. -/
  map_zero : U 0 = 1
  /-- The group law. -/
  map_add : ∀ s t, U (s + t) = U s * U t
  /-- Each `U t` is unitary. -/
  unitary : ∀ t, U t ∈ unitary (H →L[ℂ] H)
  /-- Strong continuity. -/
  strongly_continuous : ∀ x, Continuous fun t => U t x

/-- The natural domain of the infinitesimal generator of `U`: the vectors `x` for which
`t ↦ U t x` is differentiable at `0`. -/
def generatorDomain (U : ℝ → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := {x | DifferentiableAt ℝ (fun t : ℝ => U t x) 0}
  add_mem' := by
    intro x y hx hy
    have h : (fun t : ℝ => U t (x + y)) = fun t : ℝ => U t x + U t y := by
      funext t; simp
    simpa [Set.mem_setOf_eq, h] using hx.add hy
  zero_mem' := by
    simp [Set.mem_setOf_eq]
  smul_mem' := by
    intro c x hx
    have h : (fun t : ℝ => U t (c • x)) = fun t : ℝ => c • U t x := by
      funext t; simp
    simpa [Set.mem_setOf_eq, h] using hx.const_smul c

@[simp] lemma mem_generatorDomain {U : ℝ → (H →L[ℂ] H)} {x : H} :
    x ∈ generatorDomain U ↔ DifferentiableAt ℝ (fun t : ℝ => U t x) 0 := Iff.rfl

/-- The infinitesimal generator `A` of a one-parameter unitary group `U`, an unbounded
operator defined on `generatorDomain U` by `A x = -I • (d/dt) (U t x) |_{t = 0}`, so that
formally `U t = exp (t * I * A)`. -/
noncomputable def generator (U : ℝ → (H →L[ℂ] H)) : H →ₗ.[ℂ] H where
  domain := generatorDomain U
  toFun :=
    { toFun := fun x => (-Complex.I) • deriv (fun t : ℝ => U t (x : H)) 0
      map_add' := by
        intro x y
        have hx : HasDerivAt (fun t : ℝ => U t (x : H)) (deriv (fun t : ℝ => U t (x : H)) 0) 0 :=
          (x.2 : DifferentiableAt ℝ _ _).hasDerivAt
        have hy : HasDerivAt (fun t : ℝ => U t (y : H)) (deriv (fun t : ℝ => U t (y : H)) 0) 0 :=
          (y.2 : DifferentiableAt ℝ _ _).hasDerivAt
        have key : HasDerivAt (fun t : ℝ => U t ((x : H) + (y : H)))
            (deriv (fun t : ℝ => U t (x : H)) 0 + deriv (fun t : ℝ => U t (y : H)) 0) 0 := by
          simp only [map_add]
          exact hx.add hy
        show (-Complex.I) • deriv (fun t : ℝ => U t ((x : H) + (y : H))) 0 = _
        rw [key.deriv, smul_add]
      map_smul' := by
        intro c x
        have hx : HasDerivAt (fun t : ℝ => U t (x : H)) (deriv (fun t : ℝ => U t (x : H)) 0) 0 :=
          (x.2 : DifferentiableAt ℝ _ _).hasDerivAt
        have key : HasDerivAt (fun t : ℝ => U t (c • (x : H)))
            (c • deriv (fun t : ℝ => U t (x : H)) 0) 0 := by
          simp only [map_smul]
          exact hx.const_smul c
        show (-Complex.I) • deriv (fun t : ℝ => U t (c • (x : H))) 0 = _
        rw [key.deriv]
        simp only [RingHom.id_apply, smul_smul, mul_comm] }

@[simp] lemma generator_domain (U : ℝ → (H →L[ℂ] H)) :
    (generator U).domain = generatorDomain U := rfl

lemma generator_apply (U : ℝ → (H →L[ℂ] H)) (x : (generator U).domain) :
    generator U x = (-Complex.I) • deriv (fun t : ℝ => U t (x : H)) 0 := rfl

section Basic

variable {U : ℝ → (H →L[ℂ] H)}

/-- A unitary group preserves inner products. -/
lemma IsUnitaryGroup.inner_map_map (hU : IsUnitaryGroup U) (t : ℝ) (x y : H) :
    inner ℂ (U t x) (U t y) = inner ℂ x y := by
  have h : (star (U t)) * U t = 1 := (Unitary.mem_iff.mp (hU.unitary t)).1
  have : inner ℂ (U t x) (U t y) = inner ℂ x (((star (U t)) * U t) y) := by
    rw [ContinuousLinearMap.mul_apply]
    rw [← ContinuousLinearMap.adjoint_inner_right]
    rfl
  rw [this, h]
  simp

/-- If `x` is in the domain of the generator, `t ↦ U t x` has derivative `I • A x` at `0`. -/
lemma hasDerivAt_of_mem_domain (x : (generator U).domain) :
    HasDerivAt (fun t : ℝ => U t (x : H)) (Complex.I • generator U x) 0 := by
  have hx : DifferentiableAt ℝ (fun t : ℝ => U t (x : H)) 0 := x.2
  have : Complex.I • generator U x = deriv (fun t : ℝ => U t (x : H)) 0 := by
    rw [generator_apply, smul_smul]
    simp
  rw [this]
  exact hx.hasDerivAt

/-- The generator is a symmetric operator. -/
lemma generator_isFormalAdjoint (hU : IsUnitaryGroup U) :
    (generator U).IsFormalAdjoint (generator U) := by
  intro x y
  have hx := hasDerivAt_of_mem_domain x
  have hy := hasDerivAt_of_mem_domain y
  have hconst : (fun t : ℝ => inner ℂ (U t (x : H)) (U t (y : H)))
      = fun _ : ℝ => (inner ℂ (x : H) (y : H) : ℂ) := by
    funext t; exact hU.inner_map_map t _ _
  have hd := hx.inner ℂ hy
  rw [hconst] at hd
  have h0 : (inner ℂ (U 0 (x : H)) (Complex.I • generator U y) : ℂ)
      + inner ℂ (Complex.I • generator U x) (U 0 (y : H)) = 0 :=
    hd.unique (hasDerivAt_const _ _)
  rw [hU.map_zero] at h0
  simp only [ContinuousLinearMap.one_apply, inner_smul_right, inner_smul_left,
    Complex.conj_I] at h0
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h1 : Complex.I * ((inner ℂ (x : H) ((generator U) y) : ℂ)
      - (inner ℂ ((generator U) x) (y : H) : ℂ)) = 0 := by linear_combination h0
  have h2 := (mul_eq_zero.mp h1).resolve_left hI
  linear_combination -h2

end Basic

section Resolvent

variable {U : ℝ → (H →L[ℂ] H)}

/-- The vector `∫_0^∞ e^{-s} U s z ds`, used to invert `A + i`. -/
noncomputable def resolventVec (U : ℝ → (H →L[ℂ] H)) (z : H) : H :=
  ∫ s in Ioi (0 : ℝ), Real.exp (-s) • U s z

lemma continuous_integrand (hU : IsUnitaryGroup U) (z : H) :
    Continuous fun s : ℝ => Real.exp (-s) • U s z :=
  (Real.continuous_exp.comp continuous_neg).smul (hU.strongly_continuous z)

lemma norm_map_eq (hU : IsUnitaryGroup U) (t : ℝ) (x : H) : ‖U t x‖ = ‖x‖ := by
  have h := hU.inner_map_map t x x
  have h1 : ‖U t x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, h]
  nlinarith [norm_nonneg (U t x), norm_nonneg x]

lemma integrableOn_integrand (hU : IsUnitaryGroup U) (z : H) :
    IntegrableOn (fun s : ℝ => Real.exp (-s) • U s z) (Ioi (0 : ℝ)) := by
  have hdom : IntegrableOn (fun s : ℝ => Real.exp (-1 * s) * ‖z‖) (Ioi (0 : ℝ)) :=
    (exp_neg_integrableOn_Ioi 0 one_pos).mul_const _
  refine Integrable.mono' hdom (continuous_integrand hU z).aestronglyMeasurable.restrict ?_
  filter_upwards with s
  simp [norm_smul, norm_map_eq hU, abs_of_pos (Real.exp_pos _)]

/-- Translation of an integral over a half-line. -/
lemma setIntegral_Ioi_shift (g : ℝ → H) (a t : ℝ) :
    (∫ s in Ioi a, g (s + t)) = ∫ s in Ioi (a + t), g s := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self (fun s => (Ioi (a + t)).indicator g s) t]
  congr 1
  funext s
  by_cases h : a < s <;>
    simp [h, show (a + t < s + t) ↔ (a < s) by constructor <;> intro <;> linarith]

/-- Splitting off a finite piece of an integral over a half-line. -/
lemma setIntegral_Ioi_eq_sub (g : ℝ → H) (hc : Continuous g)
    (hi : IntegrableOn g (Ioi (0 : ℝ))) (t : ℝ) :
    (∫ s in Ioi t, g s) = (∫ s in Ioi (0 : ℝ), g s) - ∫ s in (0 : ℝ)..t, g s := by
  rcases le_total 0 t with h | h
  · have hsplit : (∫ s in Ioi (0 : ℝ), g s) = (∫ s in Ioc (0 : ℝ) t, g s) + ∫ s in Ioi t, g s := by
      rw [← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        hc.integrableOn_Ioc (hi.mono_set (Ioi_subset_Ioi h)), Set.Ioc_union_Ioi_eq_Ioi h]
    rw [intervalIntegral.integral_of_le h, hsplit]
    abel
  · have hsplit : (∫ s in Ioi t, g s) = (∫ s in Ioc t (0 : ℝ), g s) + ∫ s in Ioi (0 : ℝ), g s := by
      rw [← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        hc.integrableOn_Ioc hi, Set.Ioc_union_Ioi_eq_Ioi h]
    rw [intervalIntegral.integral_of_ge h, hsplit]
    abel

/-- The fundamental identity `U t (R z) = e^t (R z - ∫_0^t e^{-s} U s z ds)`. -/
lemma apply_resolventVec (hU : IsUnitaryGroup U) (z : H) (t : ℝ) :
    U t (resolventVec U z)
      = Real.exp t • (resolventVec U z - ∫ s in (0 : ℝ)..t, Real.exp (-s) • U s z) := by
  have hcont : Continuous (fun s : ℝ => Real.exp (-s) • U s z) := continuous_integrand hU z
  have hint : IntegrableOn (fun s : ℝ => Real.exp (-s) • U s z) (Ioi (0 : ℝ)) :=
    integrableOn_integrand hU z
  have step2 : ∀ s : ℝ, U t (Real.exp (-s) • U s z)
      = Real.exp t • (Real.exp (-(s + t)) • U (s + t) z) := by
    intro s
    have hUts : U t (U s z) = U (s + t) z := by
      rw [show s + t = t + s by ring, hU.map_add]
      rfl
    rw [ContinuousLinearMap.map_smul_of_tower, hUts, smul_smul, ← Real.exp_add]
    congr 1
    ring_nf
  calc U t (resolventVec U z)
      = ∫ s in Ioi (0 : ℝ), U t (Real.exp (-s) • U s z) := by
        rw [resolventVec, ContinuousLinearMap.integral_comp_comm _ hint]
    _ = ∫ s in Ioi (0 : ℝ), Real.exp t • (Real.exp (-(s + t)) • U (s + t) z) := by
        simp only [step2]
    _ = Real.exp t • ∫ s in Ioi (0 : ℝ), Real.exp (-(s + t)) • U (s + t) z :=
        integral_smul _ _
    _ = Real.exp t • ∫ s in Ioi (0 + t), Real.exp (-s) • U s z := by
        rw [show (∫ s in Ioi (0 : ℝ), Real.exp (-(s + t)) • U (s + t) z)
            = ∫ s in Ioi (0 + t), Real.exp (-s) • U s z from
          setIntegral_Ioi_shift (fun u : ℝ => Real.exp (-u) • U u z) 0 t]
    _ = Real.exp t • (resolventVec U z - ∫ s in (0 : ℝ)..t, Real.exp (-s) • U s z) := by
        rw [zero_add, setIntegral_Ioi_eq_sub _ hcont hint t]
        rfl

lemma hasDerivAt_resolventVec (hU : IsUnitaryGroup U) (z : H) :
    HasDerivAt (fun t : ℝ => U t (resolventVec U z)) (resolventVec U z - z) 0 := by
  have hcont : Continuous (fun s : ℝ => Real.exp (-s) • U s z) := continuous_integrand hU z
  have hF : HasDerivAt (fun t : ℝ => ∫ s in (0 : ℝ)..t, Real.exp (-s) • U s z)
      (Real.exp (-(0 : ℝ)) • U 0 z) 0 := (hcont.integral_hasStrictDerivAt 0 0).hasDerivAt
  have hd := (Real.hasDerivAt_exp 0).smul
    ((hasDerivAt_const (0 : ℝ) (resolventVec U z)).sub hF)
  have hfun : (fun t : ℝ => U t (resolventVec U z))
      = fun t : ℝ => Real.exp t • (resolventVec U z - ∫ s in (0 : ℝ)..t, Real.exp (-s) • U s z) :=
    funext (apply_resolventVec hU z)
  rw [hfun]
  have hd' : HasDerivAt
      (fun t : ℝ => Real.exp t • (resolventVec U z - ∫ s in (0 : ℝ)..t, Real.exp (-s) • U s z))
      (Real.exp 0 • (0 - Real.exp (-(0 : ℝ)) • U 0 z)
        + Real.exp 0 • (resolventVec U z - ∫ s in (0 : ℝ)..(0 : ℝ), Real.exp (-s) • U s z)) 0 := hd
  convert hd' using 1
  rw [hU.map_zero]
  simp
  abel

lemma resolventVec_mem (hU : IsUnitaryGroup U) (z : H) :
    resolventVec U z ∈ (generator U).domain :=
  (hasDerivAt_resolventVec hU z).differentiableAt

lemma generator_resolventVec (hU : IsUnitaryGroup U) (z : H) :
    generator U ⟨resolventVec U z, resolventVec_mem hU z⟩
      = (-Complex.I) • (resolventVec U z - z) := by
  have h := (hasDerivAt_resolventVec hU z).deriv
  rw [generator_apply]
  simp only []
  rw [h]

/-- `A + i` is surjective. -/
lemma surjective_add_I (hU : IsUnitaryGroup U) (w : H) :
    ∃ x : (generator U).domain, generator U x + Complex.I • (x : H) = w := by
  refine ⟨⟨resolventVec U ((-Complex.I) • w), resolventVec_mem hU _⟩, ?_⟩
  rw [generator_resolventVec hU]
  have hI2 : (-Complex.I) * (-Complex.I) = -1 := by
    simp [Complex.I_mul_I]
  simp only [smul_sub, smul_smul, hI2]
  module

end Resolvent

section Reverse

variable {U : ℝ → (H →L[ℂ] H)}

lemma IsUnitaryGroup.reverse (hU : IsUnitaryGroup U) : IsUnitaryGroup (fun t => U (-t)) := by
  refine ⟨by simpa using hU.map_zero, ?_, fun t => hU.unitary _, ?_⟩
  · intro s t
    have h : -(s + t) = -s + -t := by ring
    simp only [h, hU.map_add]
  · intro x
    exact (hU.strongly_continuous x).comp continuous_neg

lemma hasDerivAt_reverse {d : H} {x : H} (hx : HasDerivAt (fun t : ℝ => U t x) d 0) :
    HasDerivAt (fun t : ℝ => U (-t) x) (-d) 0 := by
  have hneg : HasDerivAt (fun t : ℝ => -t) (-1 : ℝ) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).neg
  have hx0 : HasDerivAt (fun t : ℝ => U t x) d ((fun t : ℝ => -t) 0) := by simpa using hx
  simpa using hx0.scomp (0 : ℝ) hneg

lemma mem_generatorDomain_reverse_iff (U : ℝ → (H →L[ℂ] H)) (x : H) :
    x ∈ generatorDomain (fun t => U (-t)) ↔ x ∈ generatorDomain U := by
  constructor
  · intro hx
    have h := hasDerivAt_reverse (U := fun t => U (-t)) (hx : DifferentiableAt ℝ _ _).hasDerivAt
    simpa [mem_generatorDomain] using h.differentiableAt
  · intro hx
    exact (hasDerivAt_reverse (hx : DifferentiableAt ℝ _ _).hasDerivAt).differentiableAt

lemma deriv_reverse (U : ℝ → (H →L[ℂ] H)) (x : H)
    (hx : x ∈ generatorDomain U) :
    deriv (fun t : ℝ => U (-t) x) 0 = - deriv (fun t : ℝ => U t x) 0 :=
  (hasDerivAt_reverse (hx : DifferentiableAt ℝ _ _).hasDerivAt).deriv

/-- `A - i` is surjective. -/
lemma surjective_sub_I (hU : IsUnitaryGroup U) (w : H) :
    ∃ x : (generator U).domain, generator U x - Complex.I • (x : H) = w := by
  obtain ⟨x, hx⟩ := surjective_add_I hU.reverse (-w)
  have hmem : (x : H) ∈ generatorDomain U :=
    (mem_generatorDomain_reverse_iff U (x : H)).mp x.2
  refine ⟨⟨(x : H), hmem⟩, ?_⟩
  rw [generator_apply] at hx ⊢
  rw [deriv_reverse U (x : H) hmem] at hx
  set d : H := deriv (fun t : ℝ => U t (x : H)) 0 with hd
  have hx' : Complex.I • d + Complex.I • (x : H) = -w := by
    rw [← hx]; module
  calc (-Complex.I) • d - Complex.I • (x : H)
      = -(Complex.I • d + Complex.I • (x : H)) := by module
    _ = -(-w) := by rw [hx']
    _ = w := neg_neg w

end Reverse

section SelfAdjoint

variable {U : ℝ → (H →L[ℂ] H)}

/-- For `x` in the domain, `⟪x, A x⟫` is real. -/
lemma inner_self_generator_im (hU : IsUnitaryGroup U) (x : (generator U).domain) :
    (inner ℂ (x : H) ((generator U) x) : ℂ).im = 0 := by
  refine Complex.conj_eq_iff_im.mp ?_
  rw [inner_conj_symm]
  exact generator_isFormalAdjoint hU x x

lemma dense_generatorDomain (hU : IsUnitaryGroup U) :
    Dense ((generator U).domain : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro p hp
  rw [Submodule.mem_orthogonal] at hp
  obtain ⟨x, hx⟩ := surjective_add_I hU p
  have hxp : (inner ℂ (x : H) p : ℂ) = 0 := hp _ x.2
  rw [← hx, inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K] at hxp
  have him := congrArg Complex.im hxp
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.zero_im,
    inner_self_generator_im hU x] at him
  have hxz : x = 0 := by
    have hre : ((‖(x : H)‖ : ℂ) ^ 2).re = ‖(x : H)‖ ^ 2 := by simp [pow_two, Complex.mul_re]
    have him' : ((‖(x : H)‖ : ℂ) ^ 2).im = 0 := by simp [pow_two, Complex.mul_im]
    simpa [him', hre] using him
  have hp0 : p = 0 := by
    rw [← hx, hxz]
    simp
  simpa using hp0

/-- The crucial maximality step: if `y` admits a formal adjoint value `w`, i.e.
`⟪w, v⟫ = ⟪y, A v⟫` for all `v` in the domain of `A`, then `y` is already in the domain
of `A` and `A y = w`. -/
lemma mem_domain_of_formal (hU : IsUnitaryGroup U) (y w : H)
    (hy : ∀ v : (generator U).domain, (inner ℂ w (v : H) : ℂ) = inner ℂ y ((generator U) v)) :
    ∃ hmem : y ∈ (generator U).domain, generator U ⟨y, hmem⟩ = w := by
  obtain ⟨x, hx⟩ := surjective_sub_I hU (w - Complex.I • y)
  have hw : w = (generator U) x - Complex.I • (x : H) + Complex.I • y := by
    rw [hx]; abel
  have hwAx : w - (generator U) x = Complex.I • (y - (x : H)) := by
    rw [hw, smul_sub]; abel
  have horth : ∀ p : H, (inner ℂ (y - (x : H)) p : ℂ) = 0 := by
    intro p
    obtain ⟨v, hv⟩ := surjective_add_I hU p
    have h1 : (inner ℂ y ((generator U) v) : ℂ) = inner ℂ w (v : H) := (hy v).symm
    have h2 : (inner ℂ (x : H) ((generator U) v) : ℂ) = inner ℂ ((generator U) x) (v : H) :=
      (generator_isFormalAdjoint hU x v).symm
    have h3 : (inner ℂ w (v : H) : ℂ) - inner ℂ ((generator U) x) (v : H)
        = -Complex.I * ((inner ℂ y (v : H) : ℂ) - inner ℂ (x : H) (v : H)) := by
      rw [← inner_sub_left, hwAx, inner_smul_left, inner_sub_left]
      simp
    rw [← hv, inner_sub_left, inner_add_right, inner_add_right, inner_smul_right,
      inner_smul_right, h1, h2]
    linear_combination h3
  have hu : y - (x : H) = 0 := inner_self_eq_zero.mp (horth _)
  have hyx : y = (x : H) := by rwa [sub_eq_zero] at hu
  have hmem : y ∈ (generator U).domain := hyx ▸ x.2
  refine ⟨hmem, ?_⟩
  have hsub : (⟨y, hmem⟩ : (generator U).domain) = x := Subtype.ext hyx
  rw [hsub, hw, hyx]
  abel

/-- **Stone's theorem**: the infinitesimal generator of a strongly continuous
one-parameter unitary group on a complex Hilbert space is self-adjoint. -/
theorem stone_generator (U : ℝ → (H →L[ℂ] H)) (hU : IsUnitaryGroup U) :
    IsSelfAdjoint (generator U) := by
  have hdense : Dense ((generator U).domain : Set H) := dense_generatorDomain hU
  rw [LinearPMap.isSelfAdjoint_def]
  refine le_antisymm ?_ ((generator_isFormalAdjoint hU).le_adjoint hdense)
  constructor
  · intro y hy
    obtain ⟨hmem, -⟩ := mem_domain_of_formal hU y ((generator U).adjoint ⟨y, hy⟩)
      (fun v => LinearPMap.adjoint_isFormalAdjoint hdense ⟨y, hy⟩ v)
    exact hmem
  · intro y y' hyy'
    obtain ⟨hmem, hval⟩ := mem_domain_of_formal hU (y : H) ((generator U).adjoint y)
      (fun v => LinearPMap.adjoint_isFormalAdjoint hdense y v)
    rw [← hval]
    congr 1
    exact Subtype.ext hyy'

end SelfAdjoint

end QPhys

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

