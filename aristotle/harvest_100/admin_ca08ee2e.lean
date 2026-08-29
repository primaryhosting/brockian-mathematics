import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Set Filter Topology Complex
open scoped LinearPMap

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A strongly continuous one-parameter unitary group on a complex Hilbert space `H`:
a family `U : ℝ → (H →L[ℂ] H)` with `U 0 = 1`, `U (s + t) = U s ∘ U t`, each `U t` norm
preserving (hence unitary, since the group law provides the inverse `U (-t)`), and such that
`t ↦ U t x` is continuous for every `x` (strong continuity). -/
structure IsUnitaryGroup (U : ℝ → H →L[ℂ] H) : Prop where
  map_zero : U 0 = 1
  map_add : ∀ s t, U (s + t) = (U s).comp (U t)
  norm_map : ∀ t x, ‖U t x‖ = ‖x‖
  continuous_apply : ∀ x, Continuous fun t => U t x

omit [CompleteSpace H] in
/-- Sanity check that the hypotheses are satisfiable: the constant family `U t = 1` is a
strongly continuous one-parameter unitary group. -/
theorem isUnitaryGroup_one : IsUnitaryGroup (fun _ : ℝ => (1 : H →L[ℂ] H)) where
  map_zero := rfl
  map_add := by intro s t; ext x; simp
  norm_map := by intro t x; simp
  continuous_apply := by intro x; simpa using continuous_const

namespace IsUnitaryGroup

variable {U : ℝ → H →L[ℂ] H}

/-- Each `U t` is a linear isometry. -/
def toLinearIsometry (hU : IsUnitaryGroup U) (t : ℝ) : H →ₗᵢ[ℂ] H :=
  ⟨(U t : H →ₗ[ℂ] H), hU.norm_map t⟩

omit [CompleteSpace H] in
theorem inner_map (hU : IsUnitaryGroup U) (t : ℝ) (x y : H) :
    inner ℂ (U t x) (U t y) = inner ℂ x y :=
  (hU.toLinearIsometry t).inner_map_map x y

omit [CompleteSpace H] in
/-- `U (-t)` is a two-sided inverse of `U t`. -/
theorem apply_neg_apply (hU : IsUnitaryGroup U) (t : ℝ) (x : H) : U t (U (-t) x) = x := by
  rw [← ContinuousLinearMap.comp_apply, ← hU.map_add]
  simp [hU.map_zero]

/-- The adjoint of `U t` is `U (-t)`. -/
theorem adjoint_eq (hU : IsUnitaryGroup U) (t : ℝ) :
    ContinuousLinearMap.adjoint (U t) = U (-t) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x z
  calc inner ℂ (U (-t) x) z = inner ℂ (U t (U (-t) x)) (U t z) := (hU.inner_map t _ _).symm
    _ = inner ℂ x (U t z) := by rw [hU.apply_neg_apply]

/-- Each `U t` is a unitary element of the algebra of bounded operators on `H`. -/
theorem mem_unitary (hU : IsUnitaryGroup U) (t : ℝ) : U t ∈ unitary (H →L[ℂ] H) := by
  constructor
  · show star (U t) * U t = 1
    have : star (U t) = U (-t) := hU.adjoint_eq t
    rw [this]
    show (U (-t)).comp (U t) = 1
    rw [← hU.map_add]
    simpa using hU.map_zero
  · show U t * star (U t) = 1
    have : star (U t) = U (-t) := hU.adjoint_eq t
    rw [this]
    show (U t).comp (U (-t)) = 1
    rw [← hU.map_add]
    simpa using hU.map_zero

omit [CompleteSpace H] in
/-- The time-reversed group `t ↦ U (-t)` is again a strongly continuous unitary group. -/
theorem neg (hU : IsUnitaryGroup U) : IsUnitaryGroup (fun t => U (-t)) where
  map_zero := by simpa using hU.map_zero
  map_add := by
    intro s t
    have : -(s + t) = (-s) + (-t) := by ring
    rw [this, hU.map_add]
  norm_map := fun t x => hU.norm_map (-t) x
  continuous_apply := fun x => (hU.continuous_apply x).comp continuous_neg

end IsUnitaryGroup

/-- The domain of the generator: those `x` for which `t ↦ U t x` is differentiable at `0`. -/
def genDomain (U : ℝ → H →L[ℂ] H) : Submodule ℂ H where
  carrier := {x : H | ∃ v, HasDerivAt (fun t : ℝ => U t x) v 0}
  add_mem' := by
    rintro x y ⟨v, hv⟩ ⟨w, hw⟩
    refine ⟨v + w, ?_⟩
    simpa using hv.add hw
  zero_mem' := ⟨0, by simpa using (hasDerivAt_const (0 : ℝ) (0 : H))⟩
  smul_mem' := by
    rintro c x ⟨v, hv⟩
    refine ⟨c • v, ?_⟩
    simpa using hv.const_smul c

omit [CompleteSpace H] in
theorem mem_genDomain_iff {U : ℝ → H →L[ℂ] H} {x : H} :
    x ∈ genDomain U ↔ ∃ v, HasDerivAt (fun t : ℝ => U t x) v 0 := Iff.rfl

/-- The derivative at `0` of `t ↦ U t x`, for `x` in the domain of the generator. -/
noncomputable def genVec (U : ℝ → H →L[ℂ] H) (x : genDomain U) : H :=
  Classical.choose (mem_genDomain_iff.1 x.2)

omit [CompleteSpace H] in
theorem hasDerivAt_genVec (U : ℝ → H →L[ℂ] H) (x : genDomain U) :
    HasDerivAt (fun t : ℝ => U t (x : H)) (genVec U x) 0 :=
  Classical.choose_spec (mem_genDomain_iff.1 x.2)

omit [CompleteSpace H] in
theorem genVec_eq {U : ℝ → H →L[ℂ] H} (x : genDomain U) {v : H}
    (h : HasDerivAt (fun t : ℝ => U t (x : H)) v 0) : genVec U x = v :=
  (hasDerivAt_genVec U x).unique h

/-- The generator `A` of the one-parameter group `U`, as an unbounded (partially defined)
operator.  It is normalized so that `U t = exp (i t A)`, i.e. `dU/dt (0) x = i • A x`. -/
noncomputable def gen (U : ℝ → H →L[ℂ] H) : H →ₗ.[ℂ] H where
  domain := genDomain U
  toFun :=
    { toFun := fun x => (-I) • genVec U x
      map_add' := by
        intro x y
        have hx := hasDerivAt_genVec U x
        have hy := hasDerivAt_genVec U y
        have h : HasDerivAt (fun t : ℝ => U t ((x : H) + (y : H))) (genVec U x + genVec U y) 0 := by
          simpa using hx.add hy
        rw [genVec_eq (x + y) h, smul_add]
      map_smul' := by
        intro c x
        have hx := hasDerivAt_genVec U x
        have h : HasDerivAt (fun t : ℝ => U t (c • (x : H))) (c • genVec U x) 0 := by
          simpa using hx.const_smul c
        rw [RingHom.id_apply, genVec_eq (c • x) h, smul_comm] }

omit [CompleteSpace H] in
theorem gen_apply {U : ℝ → H →L[ℂ] H} (x : genDomain U) : gen U x = (-I) • genVec U x := rfl

omit [CompleteSpace H] in
/-- The defining property of the generator: `d/dt (U t x)|_{t=0} = i • A x`. -/
theorem hasDerivAt_gen (U : ℝ → H →L[ℂ] H) (x : genDomain U) :
    HasDerivAt (fun t : ℝ => U t (x : H)) (I • gen U x) 0 := by
  have := hasDerivAt_genVec U x
  rwa [gen_apply, smul_smul, show I * -I = 1 by simp, one_smul]

omit [CompleteSpace H] in
/-- Membership in the domain, with the value of the generator recorded. -/
theorem mem_genDomain_of_hasDerivAt {U : ℝ → H →L[ℂ] H} {x v : H}
    (h : HasDerivAt (fun t : ℝ => U t x) v 0) :
    ∃ hx : x ∈ genDomain U, gen U ⟨x, hx⟩ = (-I) • v := by
  refine ⟨⟨v, h⟩, ?_⟩
  rw [gen_apply, genVec_eq ⟨x, ⟨v, h⟩⟩ h]

/-! ### Symmetry of the generator -/

omit [CompleteSpace H] in
/-- The generator is symmetric. -/
theorem gen_isFormalAdjoint {U : ℝ → H →L[ℂ] H} (hU : IsUnitaryGroup U) :
    (gen U).IsFormalAdjoint (gen U) := by
  intro x y
  have hx := hasDerivAt_gen U x
  have hy := hasDerivAt_gen U y
  have hd : HasDerivAt (fun t : ℝ => inner ℂ (U t (x : H)) (U t (y : H)))
      (inner ℂ (U 0 (x : H)) (I • gen U y) + inner ℂ (I • gen U x) (U 0 (y : H))) 0 :=
    hx.inner ℂ hy
  have hconst : (fun t : ℝ => inner ℂ (U t (x : H)) (U t (y : H)))
      = fun _ : ℝ => (inner ℂ (x : H) (y : H) : ℂ) := by
    funext t
    exact hU.inner_map t _ _
  rw [hconst] at hd
  have h0 : inner ℂ (U 0 (x : H)) (I • gen U y) + inner ℂ (I • gen U x) (U 0 (y : H)) = 0 :=
    hd.unique (hasDerivAt_const _ _)
  rw [hU.map_zero] at h0
  simp only [ContinuousLinearMap.one_apply, inner_smul_left, inner_smul_right,
    Complex.conj_I] at h0
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  field_simp at h0
  rcases mul_eq_zero.1 h0 with h | h
  · exact absurd h hI
  · linear_combination -h

/-! ### Surjectivity of `A ± i` -/

/-- Key analytic step (a resolvent construction): for every `y` there is `x` with
`d/dt (U t x)|_{t=0} = x - y`. -/
theorem stone_resolvent {U : ℝ → H →L[ℂ] H} (hU : IsUnitaryGroup U) (y : H) :
    ∃ x : H, HasDerivAt (fun t : ℝ => U t x) (x - y) 0 := by
  classical
  set g : ℝ → H := fun s => (Real.exp (-s) : ℂ) • U s y with hgdef
  have hgc : Continuous g :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).smul
      (hU.continuous_apply y)
  have hgnorm : ∀ s, ‖g s‖ = Real.exp (-s) * ‖y‖ := by
    intro s
    simp [hgdef, norm_smul, hU.norm_map, Complex.norm_exp]
  have hInt : ∀ c : ℝ, IntegrableOn g (Set.Ioi c) := by
    intro c
    have hbound : IntegrableOn (fun s : ℝ => Real.exp (-s) * ‖y‖) (Set.Ioi c) := by
      have := (exp_neg_integrableOn_Ioi c (b := 1) one_pos).mul_const ‖y‖
      simpa using this
    refine Integrable.mono' hbound hgc.aestronglyMeasurable ?_
    filter_upwards with s using le_of_eq (hgnorm s)
  have hIntervalInt : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
    hgc.intervalIntegrable a b
  set R : H := ∫ s in Set.Ioi (0 : ℝ), g s with hR
  have hg0 : g 0 = y := by simp [hgdef, hU.map_zero]
  have hkey : ∀ t : ℝ, U t R = (Real.exp t : ℂ) • ((∫ s in t..(0 : ℝ), g s) + R) := by
    intro t
    have h1 : U t R = ∫ s in Set.Ioi (0 : ℝ), U t (g s) :=
      (ContinuousLinearMap.integral_comp_comm (U t) (hInt 0)).symm
    have h2 : ∀ s : ℝ, U t (g s) = (Real.exp t : ℂ) • g (t + s) := by
      intro s
      have hUts : U (t + s) y = U t (U s y) := by
        rw [hU.map_add]; rfl
      simp only [hgdef, map_smul, hUts, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add]
      ring_nf
    have htrans : (∫ s in Set.Ioi (0 : ℝ), g (t + s)) = ∫ s in Set.Ioi t, g s := by
      have h := (measurePreserving_add_left (volume : Measure ℝ) t).setIntegral_preimage_emb
        (measurableEmbedding_addLeft t) g (Set.Ioi t)
      simpa using h
    calc U t R = ∫ s in Set.Ioi (0 : ℝ), U t (g s) := h1
      _ = ∫ s in Set.Ioi (0 : ℝ), (Real.exp t : ℂ) • g (t + s) := by simp_rw [h2]
      _ = (Real.exp t : ℂ) • ∫ s in Set.Ioi (0 : ℝ), g (t + s) := integral_smul _ _
      _ = (Real.exp t : ℂ) • ∫ s in Set.Ioi t, g s := by rw [htrans]
      _ = (Real.exp t : ℂ) • ((∫ s in t..(0 : ℝ), g s) + R) := by
          rw [intervalIntegral.integral_interval_add_Ioi (hInt t) (hInt 0)]
  refine ⟨R, ?_⟩
  have hexp : HasDerivAt (fun t : ℝ => ((Real.exp t : ℝ) : ℂ)) 1 0 := by
    have := (Real.hasDerivAt_exp 0).ofReal_comp
    simpa using this
  have hphi : HasDerivAt (fun t : ℝ => ∫ s in t..(0 : ℝ), g s) (-g 0) 0 :=
    intervalIntegral.integral_hasDerivAt_left (hIntervalInt 0 0)
      (hgc.stronglyMeasurableAtFilter _ _) hgc.continuousAt
  have hderiv : HasDerivAt (fun t : ℝ => (Real.exp t : ℂ) • ((∫ s in t..(0 : ℝ), g s) + R))
      (R - y) 0 := by
    have h := hexp.smul (hphi.add_const R)
    convert h using 1
    simp [hg0, sub_eq_neg_add]
  have hfun : (fun t : ℝ => U t R)
      = fun t : ℝ => (Real.exp t : ℂ) • ((∫ s in t..(0 : ℝ), g s) + R) := funext hkey
  rw [hfun]
  exact hderiv

theorem surjective_gen_add_I {U : ℝ → H →L[ℂ] H} (hU : IsUnitaryGroup U) (y : H) :
    ∃ x : genDomain U, gen U x + I • (x : H) = y := by
  obtain ⟨x, hx⟩ := stone_resolvent hU y
  obtain ⟨hxd, hgen⟩ := mem_genDomain_of_hasDerivAt hx
  refine ⟨(-I) • ⟨x, hxd⟩, ?_⟩
  rw [LinearPMap.map_smul, hgen]
  have hc : ((((-I) • (⟨x, hxd⟩ : genDomain U)) : genDomain U) : H) = (-I) • x := rfl
  rw [hc, smul_smul, smul_smul, smul_sub]
  rw [show (-I) * (-I) = -1 by simp [Complex.I_mul_I],
    show I * -I = 1 by simp [Complex.I_mul_I]]
  module

theorem surjective_gen_sub_I {U : ℝ → H →L[ℂ] H} (hU : IsUnitaryGroup U) (y : H) :
    ∃ x : genDomain U, gen U x - I • (x : H) = y := by
  obtain ⟨x, hx⟩ := stone_resolvent hU.neg y
  have hx' : HasDerivAt (fun t : ℝ => U t x) (y - x) 0 := by
    have hx0 : HasDerivAt (fun s : ℝ => U (-s) x) (x - y) (-0 : ℝ) := by simpa using hx
    have h := hx0.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    simp only [Function.comp_def, neg_neg, neg_smul, one_smul] at h
    simpa using h
  obtain ⟨hxd, hgen⟩ := mem_genDomain_of_hasDerivAt hx'
  refine ⟨I • ⟨x, hxd⟩, ?_⟩
  rw [LinearPMap.map_smul, hgen]
  have hc : (((I • (⟨x, hxd⟩ : genDomain U)) : genDomain U) : H) = I • x := rfl
  rw [hc, smul_smul, smul_smul, smul_sub]
  rw [show I * -I = 1 by simp [Complex.I_mul_I], show I * I = -1 by simp [Complex.I_mul_I]]
  module

theorem dense_genDomain {U : ℝ → H →L[ℂ] H} (hU : IsUnitaryGroup U) :
    Dense ((gen U).domain : Set H) := by
  have hbot : (genDomain U)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    obtain ⟨x, hx⟩ := surjective_gen_add_I hU y
    have hxy : inner ℂ (x : H) y = 0 :=
      inner_eq_zero_symm.1 ((Submodule.mem_orthogonal' _ _).1 hy _ x.2)
    rw [← hx, inner_add_right, inner_smul_right] at hxy
    have hreal : (starRingEnd ℂ) (inner ℂ (x : H) (gen U x)) = inner ℂ (x : H) (gen U x) := by
      rw [inner_conj_symm]
      exact gen_isFormalAdjoint hU x x
    have him : (inner ℂ (x : H) (gen U x)).im = 0 := Complex.conj_eq_iff_im.1 hreal
    have hxx : (inner ℂ (x : H) (x : H) : ℂ) = ((‖(x : H)‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_num
    rw [hxx] at hxy
    have hnorm : ‖(x : H)‖ ^ 2 = 0 := by
      have h1 := congrArg Complex.im hxy
      simp only [Complex.add_im, him, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, Complex.ofReal_re, Complex.zero_im] at h1
      linarith
    have hx0 : (x : H) = 0 :=
      norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hnorm)
    have hx0' : x = 0 := Subtype.ext hx0
    have hy0 : y = 0 := by
      rw [← hx, hx0']
      simp
    simpa using hy0
  have htop : (genDomain U).topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.2 hbot
  rw [show ((gen U).domain : Set H) = ((genDomain U : Submodule ℂ H) : Set H) from rfl,
    dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, htop]
  simp

/-- **Stone's theorem**: the generator of a strongly continuous one-parameter unitary group
on a complex Hilbert space is a self-adjoint (unbounded) operator. -/
theorem stone_generator {U : ℝ → H →L[ℂ] H} (hU : IsUnitaryGroup U) :
    IsSelfAdjoint (gen U) := by
  have hd := dense_genDomain hU
  have h1 : gen U ≤ (gen U)† := (gen_isFormalAdjoint hU).le_adjoint hd
  have key : ∀ (y : H) (hy : y ∈ ((gen U)†).domain),
      ∃ hx : y ∈ (gen U).domain, (gen U)† ⟨y, hy⟩ = gen U ⟨y, hx⟩ := by
    intro y hy
    set z : H := (gen U)† ⟨y, hy⟩ with hz
    have hadj : ∀ w : (gen U).domain, inner ℂ z (w : H) = inner ℂ y (gen U w) := by
      intro w
      exact LinearPMap.adjoint_isFormalAdjoint hd ⟨y, hy⟩ w
    obtain ⟨x, hx⟩ := surjective_gen_sub_I hU (z - I • y)
    have horth : ∀ w : (gen U).domain, inner ℂ (y - (x : H)) (gen U w + I • (w : H)) = 0 := by
      intro w
      have hsym : inner ℂ (x : H) (gen U w) = inner ℂ (gen U x) (w : H) :=
        (gen_isFormalAdjoint hU x w).symm
      have h3 : inner ℂ (z - I • y) (w : H) = inner ℂ (gen U x - I • (x : H)) (w : H) := by
        rw [hx]
      rw [inner_sub_left, inner_sub_left, inner_smul_left, inner_smul_left, Complex.conj_I] at h3
      rw [inner_sub_left, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right]
      linear_combination h3 - hadj w - hsym
    have hyx : y - (x : H) = 0 := by
      obtain ⟨w, hw⟩ := surjective_gen_add_I hU (y - (x : H))
      have hzero := horth w
      rw [hw] at hzero
      exact inner_self_eq_zero.1 hzero
    have hxy : (x : H) = y := (sub_eq_zero.1 hyx).symm
    refine ⟨hxy ▸ x.2, ?_⟩
    have hzz : z = gen U x := by
      rw [hxy] at hx
      exact (sub_left_inj.1 hx).symm
    rw [hzz]
    congr 1
    exact Subtype.ext hxy
  have h2 : (gen U)† ≤ gen U := by
    refine ⟨fun y hy => (key y hy).1, ?_⟩
    rintro ⟨y, hy⟩ ⟨y', hy'⟩ (h : y = y')
    subst h
    obtain ⟨hx, hval⟩ := key y hy
    exact hval
  exact le_antisymm h2 h1

end QPhys

