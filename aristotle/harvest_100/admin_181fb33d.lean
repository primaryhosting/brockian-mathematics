/-
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean does not allow a module docstring before the `import` line, so the header above is a
plain block comment; the same header is repeated as a module docstring below.)
-/
import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Stone's theorem: the infinitesimal generator of a strongly continuous one-parameter
unitary group on a complex Hilbert space is self-adjoint (as an unbounded, i.e. partially
defined, operator).
-/

namespace QPhys

open Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The domain of the infinitesimal generator of a one-parameter group `U`:
the set of vectors `x` for which the orbit map `t ↦ U t x` is differentiable at `0`. -/
def generatorDomain (U : ℝ → H →L[ℂ] H) : Submodule ℂ H where
  carrier := {x : H | ∃ y : H, HasDerivAt (fun t : ℝ => U t x) y 0}
  add_mem' := by
    rintro x x' ⟨y, hy⟩ ⟨y', hy'⟩
    refine ⟨y + y', ?_⟩
    have h : (fun t : ℝ => U t (x + x')) = fun t : ℝ => U t x + U t x' := by
      funext t; simp
    rw [h]; exact hy.add hy'
  zero_mem' := by
    refine ⟨0, ?_⟩
    have h : (fun t : ℝ => U t (0 : H)) = fun _ : ℝ => (0 : H) := by funext t; simp
    rw [h]; exact hasDerivAt_const _ _
  smul_mem' := by
    rintro c x ⟨y, hy⟩
    refine ⟨c • y, ?_⟩
    have h : (fun t : ℝ => U t (c • x)) = fun t : ℝ => c • U t x := by
      funext t; simp
    rw [h]; exact hy.const_smul c

/-- The vector-valued derivative at `0` of the orbit map `t ↦ U t x`. -/
def orbitDeriv (U : ℝ → H →L[ℂ] H) (x : H) : H := deriv (fun t : ℝ => U t x) 0

/-- The infinitesimal generator `A = i (d/dt) U(t)|_{t=0}` of a one-parameter group `U`,
as a partially defined (unbounded) operator. With this convention `U t = exp (-i t A)`. -/
def generator (U : ℝ → H →L[ℂ] H) : H →ₗ.[ℂ] H where
  domain := generatorDomain U
  toFun :=
  { toFun := fun x => Complex.I • orbitDeriv U (x : H)
    map_add' := by
      rintro ⟨x, hx⟩ ⟨x', hx'⟩
      obtain ⟨y, hy⟩ := hx
      obtain ⟨y', hy'⟩ := hx'
      have hsum : HasDerivAt (fun t : ℝ => U t (x + x')) (y + y') 0 := by
        have h : (fun t : ℝ => U t (x + x')) = fun t : ℝ => U t x + U t x' := by
          funext t; simp
        rw [h]; exact hy.add hy'
      show Complex.I • orbitDeriv U (x + x') =
        Complex.I • orbitDeriv U x + Complex.I • orbitDeriv U x'
      rw [orbitDeriv, orbitDeriv, orbitDeriv, hsum.deriv, hy.deriv, hy'.deriv, smul_add]
    map_smul' := by
      rintro c ⟨x, hx⟩
      obtain ⟨y, hy⟩ := hx
      have hsm : HasDerivAt (fun t : ℝ => U t (c • x)) (c • y) 0 := by
        have h : (fun t : ℝ => U t (c • x)) = fun t : ℝ => c • U t x := by
          funext t; simp
        rw [h]; exact hy.const_smul c
      show Complex.I • orbitDeriv U (c • x) = c • (Complex.I • orbitDeriv U x)
      rw [orbitDeriv, orbitDeriv, hsm.deriv, hy.deriv, smul_comm]
  }

@[simp] lemma generator_domain (U : ℝ → H →L[ℂ] H) :
    (generator U).domain = generatorDomain U := rfl

@[simp] lemma generator_apply (U : ℝ → H →L[ℂ] H) (x : (generator U).domain) :
    generator U x = Complex.I • orbitDeriv U (x : H) := rfl

/-- Composition of a `ℂ`-linear continuous map with a differentiable curve. -/
lemma hasDerivAt_clm_apply (L : H →L[ℂ] H) {f : ℝ → H} {v : H} {s : ℝ}
    (h : HasDerivAt f v s) : HasDerivAt (fun t : ℝ => L (f t)) (L v) s :=
  (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h

section Group

variable [CompleteSpace H] (U : ℝ → H →L[ℂ] H)
  (hU0 : ∀ x, U 0 x = x)
  (hUadd : ∀ s t x, U (s + t) x = U s (U t x))
  (hUnorm : ∀ t x, ‖U t x‖ = ‖x‖)
  (hUcont : ∀ x, Continuous fun t : ℝ => U t x)

omit [CompleteSpace H] in
include hUnorm in
/-- Each `U t` preserves the inner product. -/
lemma inner_U_U (t : ℝ) (x y : H) :
    inner ℂ (U t x) (U t y) = inner ℂ x y := by
  let L : H →ₗᵢ[ℂ] H := ⟨(U t : H →ₗ[ℂ] H), hUnorm t⟩
  exact L.inner_map_map x y

omit [CompleteSpace H] in
include hU0 hUadd in
lemma U_apply_neg (t : ℝ) (x : H) : U t (U (-t) x) = x := by
  rw [← hUadd, add_neg_cancel, hU0]

omit [CompleteSpace H] in
include hU0 hUadd hUnorm in
lemma inner_U_left (t : ℝ) (x y : H) :
    inner ℂ (U t x) y = inner ℂ x (U (-t) y) := by
  conv_lhs => rw [← U_apply_neg U hU0 hUadd t y]
  exact inner_U_U U hUnorm t x (U (-t) y)

omit [CompleteSpace H] in
/-- The derivative of the orbit map of an element of the domain. -/
lemma hasDerivAt_orbit_zero {x : H} (hx : x ∈ generatorDomain U) :
    HasDerivAt (fun t : ℝ => U t x) (orbitDeriv U x) 0 := by
  obtain ⟨y, hy⟩ := hx
  simpa [orbitDeriv, hy.deriv] using hy

omit [CompleteSpace H] in
include hUadd in
/-- The domain is invariant under the group, and the generator commutes with it. -/
lemma orbit_mem_domain {x : H} (hx : x ∈ generatorDomain U) (s : ℝ) :
    U s x ∈ generatorDomain U ∧ orbitDeriv U (U s x) = U s (orbitDeriv U x) := by
  have key : HasDerivAt (fun t : ℝ => U t (U s x)) (U s (orbitDeriv U x)) 0 := by
    have h : (fun t : ℝ => U t (U s x)) = fun t : ℝ => U s (U t x) := by
      funext t
      rw [← hUadd, ← hUadd, add_comm]
    rw [h]
    exact hasDerivAt_clm_apply (U s) (hasDerivAt_orbit_zero U hx)
  exact ⟨⟨_, key⟩, by simp [orbitDeriv, key.deriv]⟩

omit [CompleteSpace H] in
include hUadd in
/-- Differentiability of the orbit map at an arbitrary time. -/
lemma hasDerivAt_orbit {x : H} (hx : x ∈ generatorDomain U) (s : ℝ) :
    HasDerivAt (fun t : ℝ => U t x) (U s (orbitDeriv U x)) s := by
  have h1 : HasDerivAt (fun t : ℝ => U (t - s) x) (orbitDeriv U x) s := by
    have hg : HasDerivAt (fun u : ℝ => U u x) (orbitDeriv U x) (s - s) := by
      simpa using hasDerivAt_orbit_zero U hx
    exact HasDerivAt.comp_sub_const s s hg
  have h2 : HasDerivAt (fun t : ℝ => U s (U (t - s) x)) (U s (orbitDeriv U x)) s :=
    hasDerivAt_clm_apply (U s) h1
  have h : (fun t : ℝ => U s (U (t - s) x)) = fun t : ℝ => U t x := by
    funext t
    rw [← hUadd]
    ring_nf
  rwa [h] at h2

omit [CompleteSpace H] in
include hU0 hUnorm in
/-- The generator is symmetric. -/
lemma generator_isFormalAdjoint : (generator U).IsFormalAdjoint (generator U) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  have hdx := hasDerivAt_orbit_zero U hx
  have hdy := hasDerivAt_orbit_zero U hy
  have hconst : HasDerivAt (fun t : ℝ => inner ℂ (U t x) (U t y))
      (inner ℂ (U (0:ℝ) x) (orbitDeriv U y) + inner ℂ (orbitDeriv U x) (U (0:ℝ) y)) 0 :=
    hdx.inner ℂ hdy
  have hc : (fun t : ℝ => (inner ℂ (U t x) (U t y) : ℂ)) = fun _ : ℝ => (inner ℂ x y : ℂ) := by
    funext t; exact inner_U_U U hUnorm t x y
  rw [hc] at hconst
  have h0 : (inner ℂ (U (0:ℝ) x) (orbitDeriv U y) + inner ℂ (orbitDeriv U x) (U (0:ℝ) y) : ℂ) = 0 :=
    ((hasDerivAt_const (0:ℝ) (inner ℂ x y : ℂ)).unique hconst).symm
  rw [hU0 x, hU0 y] at h0
  simp only [generator_apply, inner_smul_left, inner_smul_right, Complex.conj_I]
  linear_combination (-Complex.I) * h0

omit [CompleteSpace H] in
include hUcont in
lemma orbit_intervalIntegrable (x : H) (a b : ℝ) :
    IntervalIntegrable (fun s => U s x) MeasureTheory.volume a b :=
  (hUcont x).intervalIntegrable a b

include hUcont in
/-- Fundamental theorem of calculus for the orbit map. -/
lemma orbitIntegral_hasDerivAt (x : H) (u : ℝ) :
    HasDerivAt (fun v : ℝ => ∫ s in (0:ℝ)..v, U s x) (U u x) u :=
  intervalIntegral.integral_hasDerivAt_right (orbit_intervalIntegrable U hUcont x 0 u)
    ((hUcont x).stronglyMeasurableAtFilter _ _) (hUcont x).continuousAt

include hUadd hUcont in
lemma orbitIntegral_translate (x : H) (t e : ℝ) :
    U t (∫ s in (0:ℝ)..e, U s x)
      = (∫ s in (0:ℝ)..(t + e), U s x) - ∫ s in (0:ℝ)..t, U s x := by
  have h2 : U t (∫ s in (0:ℝ)..e, U s x) = ∫ s in (0:ℝ)..e, U t (U s x) :=
    (ContinuousLinearMap.intervalIntegral_comp_comm (U t)
      (orbit_intervalIntegrable U hUcont x 0 e)).symm
  have h3 : (∫ s in (0:ℝ)..e, U t (U s x)) = ∫ s in (0:ℝ)..e, U (t + s) x := by
    refine intervalIntegral.integral_congr ?_
    intro s _
    exact (hUadd t s x).symm
  have h4 : (∫ s in (0:ℝ)..e, U (t + s) x) = ∫ s in (t + 0)..(t + e), U s x :=
    intervalIntegral.integral_comp_add_left (fun s => U s x) t
  rw [h2, h3, h4, add_zero]
  exact (intervalIntegral.integral_interval_sub_left
    (orbit_intervalIntegrable U hUcont x 0 (t + e)) (orbit_intervalIntegrable U hUcont x 0 t)).symm

include hU0 hUadd hUcont in
/-- Averages of the orbit over an interval lie in the domain of the generator. -/
lemma orbitIntegral_mem_domain (x : H) (e : ℝ) :
    (∫ s in (0:ℝ)..e, U s x) ∈ generatorDomain U := by
  refine ⟨U e x - x, ?_⟩
  have h0e : HasDerivAt (fun v : ℝ => ∫ s in (0:ℝ)..v, U s x) (U e x) (0 + e) := by
    rw [zero_add]
    exact orbitIntegral_hasDerivAt U hUcont x e
  have hA : HasDerivAt (fun t : ℝ => ∫ s in (0:ℝ)..(t + e), U s x) (U e x) 0 :=
    HasDerivAt.comp_add_const 0 e h0e
  have hB : HasDerivAt (fun t : ℝ => ∫ s in (0:ℝ)..t, U s x) x 0 := by
    simpa [hU0] using orbitIntegral_hasDerivAt U hUcont x 0
  have hsub := hA.sub hB
  have hfun : (fun t : ℝ => U t (∫ s in (0:ℝ)..e, U s x))
      = ((fun t : ℝ => ∫ s in (0:ℝ)..(t + e), U s x) - fun t : ℝ => ∫ s in (0:ℝ)..t, U s x) := by
    funext t
    simp only [Pi.sub_apply]
    exact orbitIntegral_translate U hUadd hUcont x t e
  rw [hfun]
  exact hsub

include hU0 hUadd hUcont in
/-- The domain of the generator is dense. -/
lemma dense_generatorDomain : Dense ((generator U).domain : Set H) := by
  intro x
  have hGd : HasDerivAt (fun v : ℝ => ∫ s in (0:ℝ)..v, U s x) x 0 := by
    simpa [hU0] using orbitIntegral_hasDerivAt U hUcont x 0
  have hslope := hasDerivAt_iff_tendsto_slope.mp hGd
  have heq : slope (fun v : ℝ => ∫ s in (0:ℝ)..v, U s x) 0
      = fun e : ℝ => e⁻¹ • (∫ s in (0:ℝ)..e, U s x) := by
    funext e
    simp [slope, vsub_eq_sub]
  rw [heq] at hslope
  refine mem_closure_of_tendsto hslope (Eventually.of_forall ?_)
  intro e
  have hmem : (∫ s in (0:ℝ)..e, U s x) ∈ generatorDomain U :=
    orbitIntegral_mem_domain U hU0 hUadd hUcont x e
  have hsm : ((e⁻¹ : ℝ) : ℂ) • (∫ s in (0:ℝ)..e, U s x) ∈ generatorDomain U :=
    Submodule.smul_mem _ _ hmem
  rw [Complex.coe_smul] at hsm
  exact hsm

include hU0 hUadd hUcont in
/-- For `y` in the domain of the adjoint, the inner product `⟪A w, y⟫` is computed by the
adjoint. -/
lemma inner_generator_adjoint {y : H} (hy : y ∈ (generator U).adjoint.domain)
    (w : (generator U).domain) :
    inner ℂ (generator U w) y = inner ℂ (w : H) ((generator U).adjoint ⟨y, hy⟩) := by
  have hdense := dense_generatorDomain U hU0 hUadd hUcont
  have h := LinearPMap.adjoint_isFormalAdjoint (T := generator U) hdense ⟨y, hy⟩ w
  calc inner ℂ (generator U w) y
      = (starRingEnd ℂ) (inner ℂ y (generator U w)) := (inner_conj_symm _ _).symm
    _ = (starRingEnd ℂ) (inner ℂ ((generator U).adjoint ⟨y, hy⟩) (w : H)) := by rw [h]
    _ = inner ℂ (w : H) ((generator U).adjoint ⟨y, hy⟩) := inner_conj_symm _ _

include hU0 hUadd hUcont in
/-- The key differential identity: for `x` in the domain of the generator and `y` in the domain
of the adjoint, `t ↦ ⟪U t x, y⟫` is differentiable with derivative `i ⟪U t x, A† y⟫`. -/
lemma hasDerivAt_inner_orbit {y : H} (hy : y ∈ (generator U).adjoint.domain)
    {x : H} (hx : x ∈ generatorDomain U) (t : ℝ) :
    HasDerivAt (fun t : ℝ => inner ℂ (U t x) y)
      (Complex.I * inner ℂ (U t x) ((generator U).adjoint ⟨y, hy⟩)) t := by
  set z : H := (generator U).adjoint ⟨y, hy⟩ with hzdef
  have h1 : HasDerivAt (fun t : ℝ => U t x) (U t (orbitDeriv U x)) t :=
    hasDerivAt_orbit U hUadd hx t
  have h2 := h1.inner ℂ (hasDerivAt_const t y)
  have hUtx : U t x ∈ generatorDomain U := (orbit_mem_domain U hUadd hx t).1
  have hgen : generator U ⟨U t x, hUtx⟩ = U t (Complex.I • orbitDeriv U x) := by
    show Complex.I • orbitDeriv U (U t x) = _
    rw [(orbit_mem_domain U hUadd hx t).2, map_smul]
  have hkey := inner_generator_adjoint U hU0 hUadd hUcont hy ⟨U t x, hUtx⟩
  rw [hgen, map_smul, inner_smul_left, Complex.conj_I] at hkey
  have hI : (Complex.I : ℂ) * Complex.I = -1 := Complex.I_mul_I
  have h3 : inner ℂ (U t (orbitDeriv U x)) y = Complex.I * inner ℂ (U t x) z := by
    linear_combination Complex.I * hkey + (inner ℂ (U t (orbitDeriv U x)) y : ℂ) * hI
  simpa [h3] using h2

include hU0 hUadd hUnorm hUcont in
/-- Integrated form of the differential identity. -/
lemma adjoint_orbit_eq {y : H} (hy : y ∈ (generator U).adjoint.domain) (tau : ℝ) :
    U (-tau) y - y
      = ∫ s in (0:ℝ)..tau, Complex.I • U (-s) ((generator U).adjoint ⟨y, hy⟩) := by
  set z : H := (generator U).adjoint ⟨y, hy⟩ with hzdef
  have hdense := dense_generatorDomain U hU0 hUadd hUcont
  refine Dense.eq_of_inner_right (K := (generator U).domain) hdense ?_
  rintro ⟨x, hx⟩
  have hx' : x ∈ generatorDomain U := hx
  have hcont : Continuous fun s : ℝ => Complex.I * inner ℂ (U s x) z :=
    continuous_const.mul ((hUcont x).inner continuous_const)
  have hint : (∫ s in (0:ℝ)..tau, Complex.I * inner ℂ (U s x) z)
      = inner ℂ (U tau x) y - inner ℂ (U 0 x) y :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hasDerivAt_inner_orbit U hU0 hUadd hUcont hy hx' s)
      (hcont.intervalIntegrable _ _)
  have hcontz : Continuous fun s : ℝ => Complex.I • U (-s) z :=
    (((hUcont z).comp continuous_neg)).const_smul Complex.I
  have hswap : inner ℂ x (∫ s in (0:ℝ)..tau, Complex.I • U (-s) z)
      = ∫ s in (0:ℝ)..tau, inner ℂ x (Complex.I • U (-s) z) := by
    have := (ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℂ x)
      (a := (0:ℝ)) (b := tau) (μ := MeasureTheory.volume)
      (hcontz.intervalIntegrable 0 tau)).symm
    simpa using this
  have hpt : ∀ s : ℝ, inner ℂ x (Complex.I • U (-s) z) = Complex.I * inner ℂ (U s x) z := by
    intro s
    rw [inner_smul_right, inner_U_left U hU0 hUadd hUnorm s x z]
  rw [hswap]
  simp only [hpt]
  rw [hint, inner_sub_right, inner_U_left U hU0 hUadd hUnorm tau x y, hU0 x]

include hU0 hUadd hUnorm hUcont in
/-- Every vector in the domain of the adjoint is in the domain of the generator, with the
expected derivative. -/
lemma orbit_hasDerivAt_of_adjoint {y : H} (hy : y ∈ (generator U).adjoint.domain) :
    HasDerivAt (fun t : ℝ => U t y) (-(Complex.I • (generator U).adjoint ⟨y, hy⟩)) 0 := by
  set z : H := (generator U).adjoint ⟨y, hy⟩ with hzdef
  have hcontz : Continuous fun s : ℝ => Complex.I • U (-s) z :=
    (((hUcont z).comp continuous_neg)).const_smul Complex.I
  have hFTC : HasDerivAt (fun tau : ℝ => ∫ s in (0:ℝ)..tau, Complex.I • U (-s) z)
      (Complex.I • U (-(0:ℝ)) z) 0 :=
    intervalIntegral.integral_hasDerivAt_right (hcontz.intervalIntegrable _ _)
      (hcontz.stronglyMeasurableAtFilter _ _) hcontz.continuousAt
  have hfun : (fun tau : ℝ => U (-tau) y - y)
      = fun tau : ℝ => ∫ s in (0:ℝ)..tau, Complex.I • U (-s) z := by
    funext tau
    exact adjoint_orbit_eq U hU0 hUadd hUnorm hUcont hy tau
  have h1 : HasDerivAt (fun tau : ℝ => U (-tau) y - y) (Complex.I • z) 0 := by
    rw [hfun]
    simpa [hU0] using hFTC
  have h2 : HasDerivAt (fun tau : ℝ => U (-tau) y) (Complex.I • z) 0 := by
    simpa using h1.add_const y
  have h2' : HasDerivAt (fun tau : ℝ => U (-tau) y) (Complex.I • z) (-(0:ℝ)) := by
    simpa using h2
  have h3 := h2'.scomp (𝕜 := ℝ) 0 (hasDerivAt_neg (0:ℝ))
  have h4 : ((fun tau : ℝ => U (-tau) y) ∘ (Neg.neg : ℝ → ℝ)) = fun t : ℝ => U t y := by
    funext t
    simp
  rw [h4] at h3
  simpa using h3

include hU0 hUadd hUnorm hUcont in
/-- The adjoint of the generator is contained in the generator. -/
lemma adjoint_le_generator : (generator U).adjoint ≤ generator U := by
  have hdomle : (generator U).adjoint.domain ≤ (generator U).domain := fun y hy =>
    ⟨_, orbit_hasDerivAt_of_adjoint U hU0 hUadd hUnorm hUcont hy⟩
  refine ⟨hdomle, ?_⟩
  rintro ⟨y, hy⟩ ⟨y', hy'⟩ hyy
  have hyy' : y = y' := hyy
  subst hyy'
  have hderiv := orbit_hasDerivAt_of_adjoint U hU0 hUadd hUnorm hUcont hy
  show (generator U).adjoint ⟨y, hy⟩ = Complex.I • orbitDeriv U y
  rw [orbitDeriv, hderiv.deriv, smul_neg, smul_smul, Complex.I_mul_I]
  simp

include hU0 hUadd hUnorm hUcont in
/-- **Stone's theorem**: the infinitesimal generator of a strongly continuous one-parameter
unitary group on a complex Hilbert space is self-adjoint.

Here `U : ℝ → H →L[ℂ] H` is a one-parameter group (`hU0`, `hUadd`) of isometries (`hUnorm`) —
these together make each `U t` unitary, since `U (-t)` is a two-sided inverse of `U t` — which is
strongly continuous (`hUcont`).  Its generator `A = i (d/dt) U(t)|_{t=0}`, an unbounded operator
defined on the dense subspace `generatorDomain U` of vectors with differentiable orbit, satisfies
`A† = A`. -/
theorem stone_generator : IsSelfAdjoint (generator U) := by
  rw [LinearPMap.isSelfAdjoint_def]
  refine le_antisymm (adjoint_le_generator U hU0 hUadd hUnorm hUcont) ?_
  exact LinearPMap.IsFormalAdjoint.le_adjoint (dense_generatorDomain U hU0 hUadd hUcont)
    (generator_isFormalAdjoint U hU0 hUnorm)

end Group

/-- Sanity check that the hypotheses of `QPhys.stone_generator` are satisfiable: the trivial
one-parameter group on `ℂ` is strongly continuous and unitary. -/
example : IsSelfAdjoint (generator (fun _ : ℝ => (1 : ℂ →L[ℂ] ℂ))) :=
  stone_generator _ (by simp) (by simp) (by simp) (fun _ => continuous_const)

end

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

