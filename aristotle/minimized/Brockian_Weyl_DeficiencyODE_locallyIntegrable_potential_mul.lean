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

import Brockian.Weyl.Primitive

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Deficiency elements of a Sturm–Liouville operator are genuine ODE solutions

Let `q : ℝ → ℝ` be a continuous potential on an interval `(a, b)` and let `lam : ℂ`.  The
*minimal operator* associated with the formally symmetric differential expression
`τ u = -u'' + q u` is the restriction of `τ` to smooth compactly supported functions in
`(a, b)`.  A function `y ∈ L²(a, b)` lies in the deficiency space of the minimal operator
at `lam` exactly when it is orthogonal to the range of `τ - conj lam` on test functions,
that is when
`∫ conj (y x) * (-(g'' x) + q x * g x - conj lam * g x) = 0`
for every test function `g` supported in `(a, b)`; see `InDeficiencySpace`.

The main theorem `deficiencyRepresentsODE_of_weakRegularity` states that the deficiency
space is exactly the space of `L²` solutions of the ordinary differential equation
`-u'' + q u = lam * u`, i.e. every deficiency element is (a.e. equal to) a genuine, twice
differentiable, classical solution of the ODE.

The hard direction rests on the one-dimensional elliptic regularity statement
`weakRegularity` (Weyl's lemma): a locally integrable distributional solution of
`-y'' + q y = lam y` agrees a.e. with a classical solution.  It is proved here, so the
main theorem is unconditional.
-/

namespace Brockian.Weyl.DeficiencyODE

open MeasureTheory Set Function Brockian.Weyl

/-- The smoothness exponent `∞`. -/
local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- `IsODESolutionOn q lam s u` says that `u` is a classical solution of
`-u'' + q u = lam * u` on the set `s`: `u` is differentiable with a differentiable
derivative `u'` and `u'' = (q - lam) * u` on `s`. -/

theorem locallyIntegrable_potential_mul (hq : Continuous q) {y : ℝ → ℂ}
    (hy : LocallyIntegrable y volume) :
    LocallyIntegrable (fun t => ((q t : ℂ) - lam) * y t) volume := by
  refine locallyIntegrable_iff.2 fun K hK => ?_
  exact IntegrableOn.continuousOn_mul
    (((Complex.continuous_ofReal.comp hq).sub continuous_const).continuousOn)
    (hy.integrableOn_isCompact hK) hK

/-- The deficiency condition, tested against real test functions, is the weak formulation
of the differential equation `-y'' + q y = lam y`. -/

theorem IsBumpOn.integrable {a b : ℝ} {g : ℝ → ℝ} (hg : IsBumpOn a b g) :
    Integrable g volume :=
  hg.continuous.integrable_of_hasCompactSupport hg.compactSupport

theorem IsBumpOn.hasDerivAt {a b : ℝ} {g : ℝ → ℝ} (hg : IsBumpOn a b g) (x : ℝ) :
    HasDerivAt g (deriv g x) x :=
  (hg.smooth.differentiable (by simp) x).hasDerivAt

/-- Integration by parts against the identity: `∫ g' x * x = -∫ g`. -/

theorem IsBumpOn.integral_deriv_mul_id {a b : ℝ} (hab : a < b) {g : ℝ → ℝ}
    (hg : IsBumpOn a b g) : ∫ x, deriv g x * x = -∫ x, g x := by
  obtain ⟨a₀, b₀, ha₀, hab₀, hb₀, hsub⟩ := hg.exists_Ioo hab
  have hgz : ∀ x, x ∉ Set.Ioo a₀ b₀ → g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hx' => hx (hsub hx')
  have hdz : ∀ x, x ∉ Set.Ioo a₀ b₀ → deriv g x = 0 := by
    intro x hx
    have hts : tsupport (deriv g) ⊆ Set.Ioo a₀ b₀ :=
      (closure_minimal support_deriv_subset isClosed_closure).trans hsub
    exact image_eq_zero_of_notMem_tsupport fun hx' => hx (hts hx')
  have hcont : Continuous (deriv g) := hg.deriv_isBumpOn.continuous
  have h1 : ∫ x, deriv g x * x = ∫ x in a₀..b₀, deriv g x * x := by
    refine integral_eq_intervalIntegral hab₀.le ?_
    intro x hx
    have : deriv g x = 0 := hdz x fun hmem => hx (Set.Ioo_subset_Ioc_self hmem)
    simp [this]
  have h2 : ∫ x, g x = ∫ x in a₀..b₀, g x := by
    refine integral_eq_intervalIntegral hab₀.le ?_
    intro x hx
    exact hgz x fun hmem => hx (Set.Ioo_subset_Ioc_self hmem)
  have hparts : ∫ x in a₀..b₀, (deriv g x * x + g x * 1) = g b₀ * b₀ - g a₀ * a₀ :=
    intervalIntegral.integral_deriv_mul_eq_sub (u := g) (u' := deriv g) (v := id)
      (v' := fun _ => 1) (fun x _ => hg.hasDerivAt x) (fun x _ => hasDerivAt_id x)
      (hcont.intervalIntegrable _ _) intervalIntegrable_const
  have hb : g b₀ = 0 := hgz b₀ (by simp)
  have ha : g a₀ = 0 := hgz a₀ (by simp)
  rw [hb, ha] at hparts
  simp only [mul_one, zero_mul, sub_self] at hparts
  have hsplit : (∫ x in a₀..b₀, (deriv g x * x + g x))
      = (∫ x in a₀..b₀, deriv g x * x) + ∫ x in a₀..b₀, g x :=
    intervalIntegral.integral_add ((hcont.mul continuous_id).intervalIntegrable _ _)
      (hg.continuous.intervalIntegrable _ _)
  rw [hsplit] at hparts
  rw [h1, h2]
  linarith [hparts]

/-- **du Bois-Reymond lemma**: a locally integrable function whose distributional derivative
vanishes on `Ioo a b` is a.e. constant there. -/

theorem IsBumpOn.absolutelyContinuousOnInterval {a b : ℝ} {g : ℝ → ℝ} (hg : IsBumpOn a b g)
    (p r : ℝ) : AbsolutelyContinuousOnInterval g p r := by
  have hderiv : ∀ x, HasDerivAt g (deriv g x) x := hg.hasDerivAt
  have hcont : Continuous (deriv g) := hg.deriv_isBumpOn.continuous
  have hrepr : g = fun x => g p + ∫ t in p..x, deriv g t := by
    funext x
    rw [intervalIntegral.integral_deriv_eq_sub (fun t _ => (hderiv t).differentiableAt)
      (hcont.intervalIntegrable _ _)]
    ring
  rw [hrepr]
  have h1 : AbsolutelyContinuousOnInterval (fun _ : ℝ => g p) p r :=
    (LipschitzWith.const (g p)).lipschitzOnWith.absolutelyContinuousOnInterval
  have h2 : AbsolutelyContinuousOnInterval (fun x => ∫ t in p..x, deriv g t) p r :=
    ((hcont.intervalIntegrable _ _).absolutelyContinuousOnInterval_intervalIntegral
      left_mem_uIcc)
  exact h1.add h2

/-- The primitive of a locally integrable function is absolutely continuous on any
interval. -/

theorem continuous (hg : IsBumpOn a b g) : Continuous g := hg.smooth.continuous

theorem deriv_isBumpOn (hg : IsBumpOn a b g) : IsBumpOn a b (deriv g) where
  smooth := (contDiff_infty_iff_deriv.1 hg.smooth).2
  compactSupport := hg.compactSupport.deriv
  tsupport_subset :=
    (closure_minimal support_deriv_subset isClosed_closure).trans hg.tsupport_subset

theorem add (hg : IsBumpOn a b g) {h : ℝ → ℝ} (hh : IsBumpOn a b h) :
    IsBumpOn a b (fun x => g x + h x) where
  smooth := hg.smooth.add hh.smooth
  compactSupport := hg.compactSupport.add hh.compactSupport
  tsupport_subset :=
    (tsupport_add g h).trans (union_subset hg.tsupport_subset hh.tsupport_subset)

theorem smul (c : ℝ) (hg : IsBumpOn a b g) : IsBumpOn a b (fun x => c * g x) where
  smooth := contDiff_const.mul hg.smooth
  compactSupport := hg.compactSupport.mul_left
  tsupport_subset := by
    refine subset_trans ?_ hg.tsupport_subset
    exact closure_mono (Function.support_mul_subset_right _ _)

theorem sub (hg : IsBumpOn a b g) {h : ℝ → ℝ} (hh : IsBumpOn a b h) :
    IsBumpOn a b (fun x => g x - h x) := by
  have := hg.add (hh.smul (-1))
  simpa [sub_eq_add_neg] using this

end IsBumpOn

/-- A compact subset of `Ioo a b` is contained in a strictly smaller open interval. -/

theorem exists_Ioo_of_isCompact {a b : ℝ} (hab : a < b) {K : Set ℝ} (hcomp : IsCompact K)
    (hsub : K ⊆ Set.Ioo a b) :
    ∃ a₀ b₀ : ℝ, a < a₀ ∧ a₀ < b₀ ∧ b₀ < b ∧ K ⊆ Set.Ioo a₀ b₀ := by
  rcases eq_empty_or_nonempty K with hK | hK
  · refine ⟨a + (b - a) / 3, a + 2 * (b - a) / 3, by linarith, by linarith, by linarith, ?_⟩
    rw [hK]; exact empty_subset _
  · have hm : sInf K ∈ K := hcomp.sInf_mem hK
    have hM : sSup K ∈ K := hcomp.sSup_mem hK
    have hmI := hsub hm
    have hMI := hsub hM
    simp only [mem_Ioo] at hmI hMI
    refine ⟨(a + sInf K) / 2, (sSup K + b) / 2, by linarith [hmI.1], ?_, by linarith [hMI.2], ?_⟩
    · have : sInf K ≤ sSup K := le_csSup hcomp.bddAbove hm
      linarith [hmI.1, hMI.2]
    · intro x hx
      have h1 : sInf K ≤ x := csInf_le hcomp.bddBelow hx
      have h2 : x ≤ sSup K := le_csSup hcomp.bddAbove hx
      simp only [mem_Ioo]
      constructor <;> linarith [hmI.1, hMI.2]

/-- The support of a bump on `Ioo a b` is contained in a strictly smaller open interval. -/

theorem IsBumpOn.exists_Ioo {a b : ℝ} {g : ℝ → ℝ} (hg : IsBumpOn a b g) (hab : a < b) :
    ∃ a₀ b₀ : ℝ, a < a₀ ∧ a₀ < b₀ ∧ b₀ < b ∧ tsupport g ⊆ Set.Ioo a₀ b₀ :=
  exists_Ioo_of_isCompact hab hg.compactSupport hg.tsupport_subset

/-- If a function vanishes outside `Ioc a₀ b₀` then its integral over the line is the
interval integral over `a₀..b₀`. -/

theorem integral_eq_intervalIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a₀ b₀ : ℝ} (hab : a₀ ≤ b₀) {F : ℝ → E} (hF : ∀ x ∉ Set.Ioc a₀ b₀, F x = 0) :
    ∫ x, F x = ∫ x in a₀..b₀, F x := by
  rw [intervalIntegral.integral_of_le hab]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero hF).symm

/-- A bump times a locally integrable function is integrable. -/

theorem IsBumpOn.integrable_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} {g : ℝ → ℝ} (hg : IsBumpOn a b g) {f : ℝ → E}
    (hf : LocallyIntegrable f volume) : Integrable (fun x => g x • f x) volume := by
  have hK : IsCompact (tsupport g) := hg.compactSupport
  have hfK : IntegrableOn f (tsupport g) volume := hf.integrableOn_isCompact hK
  have hint : IntegrableOn (fun x => g x • f x) (tsupport g) volume :=
    hfK.continuousOn_smul hg.continuous.continuousOn hK
  refine hint.integrable_of_forall_notMem_eq_zero ?_
  intro x hx
  have : g x = 0 := image_eq_zero_of_notMem_tsupport hx
  simp [this]

/-- The primitive of a bump with vanishing integral is again a bump, with derivative the
original bump. -/

theorem IsBumpOn.antideriv {a b : ℝ} (hab : a < b) {g : ℝ → ℝ} (hg : IsBumpOn a b g)
    (h0 : ∫ x, g x = 0) :
    IsBumpOn a b (fun x => ∫ t in a..x, g t) ∧
      ∀ x, HasDerivAt (fun x => ∫ t in a..x, g t) (g x) x := by
  have hcont : Continuous g := hg.continuous
  have hderiv : ∀ x, HasDerivAt (fun x => ∫ t in a..x, g t) (g x) x := fun x =>
    (hcont.integral_hasStrictDerivAt a x).hasDerivAt
  obtain ⟨a₀, b₀, ha₀, hab₀, hb₀, hsub⟩ := hg.exists_Ioo hab
  have hzero : ∀ x, x ∉ Set.Ioo a₀ b₀ → g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hx' => hx (hsub hx')
  have hsupp : ∀ x, x ∉ Set.Icc a₀ b₀ → (∫ t in a..x, g t) = 0 := by
    intro x hx
    rcases lt_or_ge x a₀ with hlt | hge
    · have hcongr : ∀ t ∈ Set.uIcc a x, g t = (0 : ℝ) := by
        intro t ht
        refine hzero t ?_
        simp only [mem_uIcc] at ht
        intro htI
        rcases ht with ht | ht
        · linarith [htI.1, ht.1]
        · linarith [htI.1, ht.2]
      calc (∫ t in a..x, g t) = ∫ _t in a..x, (0 : ℝ) :=
            intervalIntegral.integral_congr hcongr
        _ = 0 := by simp
    · have hxb : b₀ < x := by
        simp only [mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx
        · linarith
        · exact hx
      have h1 : ∀ t ∉ Set.Ioc a x, g t = 0 := by
        intro t ht
        refine hzero t ?_
        simp only [mem_Ioc, not_and_or, not_le, not_lt] at ht
        intro htI
        rcases ht with ht | ht
        · linarith [htI.1]
        · linarith [htI.2]
      rw [intervalIntegral.integral_of_le (by linarith),
        setIntegral_eq_integral_of_forall_compl_eq_zero h1, h0]
  refine ⟨⟨?_, ?_, ?_⟩, hderiv⟩
  · rw [contDiff_infty_iff_deriv]
    refine ⟨fun x => (hderiv x).differentiableAt, ?_⟩
    have hd : deriv (fun x => ∫ t in a..x, g t) = g := funext fun x => (hderiv x).deriv
    rw [hd]
    exact hg.smooth
  · exact HasCompactSupport.intro (isCompact_Icc (a := a₀) (b := b₀)) hsupp
  · have h1 : tsupport (fun x => ∫ t in a..x, g t) ⊆ Set.Icc a₀ b₀ := by
      refine closure_minimal ?_ isClosed_Icc
      intro x hx
      by_contra hxc
      exact hx (hsupp x hxc)
    exact h1.trans (Set.Icc_subset_Ioo ha₀ hb₀)

/-- There is a bump function on `Ioo a b` with integral one. -/
