import Mathlib

/-!
# Goldstone
Category: Frontier Phys
Target: Phys.goldstone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` lines to precede any module docstring, so the required
header comment appears immediately after the single `import Mathlib` line.)

## Statement

Spontaneous breaking of a continuous global symmetry yields a massless mode (Goldstone).

We work with a scalar potential `V : E → ℝ` on a real normed space `E` of field values,
assumed `C²`.  A *vacuum* is a local minimum `v` of `V`.  The *mass form* at `v` is the
Hessian `massForm V v = D²V(v)`, whose matrix in an orthonormal basis is the mass matrix
`M_{ij} = ∂_i∂_j V(v)` of the quadratic fluctuations around `v`; a nonzero vector in its
kernel is a zero-eigenvalue direction, i.e. a **massless mode**.

A *continuous global symmetry* is a smooth one-parameter group `R : ℝ → (E →L[ℝ] E)`
(`R (s+t) = R s ∘ R t`, `R 0 = id`) of linear transformations of the field values leaving
the potential invariant: `V (R t x) = V x`.  It is *spontaneously broken* at the vacuum `v`
when `v` itself is not invariant, i.e. `R t v ≠ v` for some `t`.

`Phys.goldstone` then produces a nonzero `X` in the kernel of the mass form.
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

open Set Filter Topology

namespace Phys

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **mass form** (Hessian of the potential) of a scalar potential `V` at a
configuration `v`.  In finite dimensions, in an orthonormal basis, this is the mass matrix
`M_{ij} = ∂_i ∂_j V (v)` of the small fluctuations around `v`; a nonzero vector in its
kernel is a **massless mode**. -/
noncomputable def massForm (V : E → ℝ) (v : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ V) v

/-- For a `C²` potential, `fderiv V` is differentiable with derivative the mass form. -/
lemma hasFDerivAt_massForm (V : E → ℝ) (hV : ContDiff ℝ 2 V) (x : E) :
    HasFDerivAt (fderiv ℝ V) (massForm V x) x :=
  ((hV.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt

/-- The mass form is a symmetric bilinear form. -/
lemma massForm_symm (V : E → ℝ) (hV : ContDiff ℝ 2 V) (x v w : E) :
    massForm V x v w = massForm V x w v :=
  second_derivative_symmetric (f' := fderiv ℝ V)
    (fun y => (hV.differentiable (by norm_num) y).hasFDerivAt)
    (hasFDerivAt_massForm V hV x) v w

/-- Differentiating the directional derivative of `V` along a `C²` curve `γ`:
`(V ∘ γ)'' = D²V(γ)(γ', γ') + DV(γ)(γ'')`. -/
lemma hasDerivAt_dirDeriv (V : E → ℝ) (hV : ContDiff ℝ 2 V)
    (γ : ℝ → E) (hγ : ContDiff ℝ 2 γ) (t : ℝ) :
    HasDerivAt (fun s => fderiv ℝ V (γ s) (deriv γ s))
      (massForm V (γ t) (deriv γ t) (deriv γ t)
        + fderiv ℝ V (γ t) (deriv (deriv γ) t)) t := by
  have hc : HasDerivAt (fun s => fderiv ℝ V (γ s)) (massForm V (γ t) (deriv γ t)) t :=
    (hasFDerivAt_massForm V hV (γ t)).comp_hasDerivAt t
      ((hγ.differentiable (by norm_num) t).hasDerivAt)
  have h2 : ContDiff ℝ (1 + 1) γ := by norm_num; exact hγ
  have hu : HasDerivAt (deriv γ) (deriv (deriv γ) t) t :=
    ((h2.deriv'.differentiable (by norm_num)) t).hasDerivAt
  exact hc.clm_apply hu

/-- One-dimensional second derivative test: the second derivative of a real function at a
local minimum is nonnegative. -/
lemma second_deriv_nonneg_of_isLocalMin {f g : ℝ → ℝ} {c : ℝ}
    (hf : ∀ t, HasDerivAt f (g t) t) (hmin : IsLocalMin f 0)
    (hg : HasDerivAt g c 0) : 0 ≤ c := by
  by_contra hcon
  push_neg at hcon
  have hg0 : g 0 = 0 := hmin.hasDerivAt_eq_zero (hf 0)
  have hslope : Filter.Tendsto (slope g 0) (𝓝[≠] (0 : ℝ)) (𝓝 c) :=
    hasDerivAt_iff_tendsto_slope.mp hg
  have h1 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), slope g 0 t < 0 := hslope.eventually_lt_const hcon
  have h1' : ∀ᶠ t in 𝓝[>] (0 : ℝ), g t < 0 := by
    have h1'' : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope g 0 t < 0 :=
      nhdsWithin_mono _ (fun x hx => (mem_Ioi.mp hx).ne') h1
    filter_upwards [h1'', self_mem_nhdsWithin] with t ht htpos
    rw [slope_def_field, hg0] at ht
    simp only [sub_zero, div_neg_iff] at ht
    rcases ht with ⟨h, h'⟩ | ⟨h, _⟩
    · exact absurd (mem_Ioi.mp htpos) (by linarith)
    · exact h
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), f 0 ≤ f t := nhdsWithin_le_nhds hmin
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (h1'.and h2)
  have hδ0 : (0 : ℝ) < δ := mem_Ioi.mp hδ
  have hb0 : (0 : ℝ) < δ / 2 := by linarith
  have hbδ : δ / 2 < δ := by linarith
  obtain ⟨c₀, hc₀, hc₀eq⟩ := exists_hasDerivAt_eq_slope f g hb0
    (fun x _ => (hf x).continuousAt.continuousWithinAt) (fun x _ => hf x)
  have hneg : g c₀ < 0 := (hsub ⟨hc₀.1, lt_trans hc₀.2 hbδ⟩).1
  have hfb : f 0 ≤ f (δ / 2) := (hsub ⟨hb0, hbδ⟩).2
  rw [hc₀eq] at hneg
  have hnn : 0 ≤ (f (δ / 2) - f 0) / (δ / 2 - 0) := div_nonneg (by linarith) (by linarith)
  linarith

/-- At a (local) minimum of the potential the mass form is positive semidefinite:
all squared masses are nonnegative. -/
lemma massForm_nonneg (V : E → ℝ) (hV : ContDiff ℝ 2 V) {v : E} (hmin : IsLocalMin V v)
    (w : E) : 0 ≤ massForm V v w w := by
  set γ : ℝ → E := fun s => v + s • w with hγdef
  have hγC : ContDiff ℝ 2 γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hd : ∀ t : ℝ, HasDerivAt γ w t := fun t => by
    have h1 : HasDerivAt (fun s : ℝ => s • w) w t := by
      simpa using (hasDerivAt_id t).smul_const w
    exact h1.const_add v
  have hderiv : deriv γ = fun _ : ℝ => w := funext fun t => (hd t).deriv
  have hderiv2 : deriv (deriv γ) = fun _ : ℝ => (0 : E) := by
    rw [hderiv]; exact funext fun t => deriv_const t w
  have hγ0 : γ 0 = v := by simp [hγdef]
  have hf : ∀ t : ℝ, HasDerivAt (fun s => V (γ s)) (fderiv ℝ V (γ t) w) t := fun t =>
    ((hV.differentiable (by norm_num) (γ t)).hasFDerivAt).comp_hasDerivAt t (hd t)
  have hminV : IsLocalMin V (γ 0) := by rw [hγ0]; exact hmin
  have hmin0 : IsLocalMin (fun s => V (γ s)) 0 :=
    hminV.comp_continuous hγC.continuous.continuousAt
  have hg := hasDerivAt_dirDeriv V hV γ hγC 0
  rw [hderiv2, hderiv, hγ0] at hg
  simp only [map_zero, add_zero] at hg
  exact second_deriv_nonneg_of_isLocalMin hf hmin0 hg

/-- A vector on which a positive semidefinite symmetric bilinear form vanishes lies in the
kernel of the form (Cauchy–Schwarz). -/
lemma clm_apply_eq_zero_of_quadratic_eq_zero {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hpsd : ∀ w, 0 ≤ B w w) (hsymm : ∀ v w, B v w = B w v) {X : E} (hX : B X X = 0) :
    B X = 0 := by
  ext w
  show B X w = 0
  by_contra ha
  have hb : 0 ≤ B w w := hpsd w
  set a : ℝ := B X w with hadef
  set b : ℝ := B w w with hbdef
  set ep : ℝ := 1 / (b + 1) with hepdef
  have hep : 0 < ep := by positivity
  have hepb : ep * b < 1 := by
    rw [hepdef, div_mul_eq_mul_div, one_mul, div_lt_one (by linarith)]
    linarith
  set t : ℝ := -(a * ep) with htdef
  have key : 0 ≤ B (X + t • w) (X + t • w) := hpsd _
  have expand : B (X + t • w) (X + t • w) = B X X + t * a + t * (B w X) + t * t * b := by
    simp [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      hadef, hbdef]
    ring
  rw [expand, hX, hsymm w X, ← hadef] at key
  have ha2 : 0 < a ^ 2 := lt_of_le_of_ne (sq_nonneg a) (Ne.symm (pow_ne_zero 2 ha))
  have e1 : 0 + t * a + t * a + t * t * b = a ^ 2 * ep * (ep * b - 2) := by
    rw [htdef]; ring
  rw [e1] at key
  have hneg : a ^ 2 * ep * (ep * b - 2) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos ha2 hep) (by linarith)
  linarith

/-- **Goldstone's theorem, curve form.**  If a `C²` potential `V` is constant along a `C²`
curve `γ` through a vacuum `v = γ 0` (a local minimum of `V`), then the velocity `γ'(0)` of
the curve lies in the kernel of the mass form: it is a massless mode. -/
theorem goldstone_of_curve (V : E → ℝ) (hV : ContDiff ℝ 2 V) {v : E} (hmin : IsLocalMin V v)
    (γ : ℝ → E) (hγ : ContDiff ℝ 2 γ) (hγ0 : γ 0 = v) (hinv : ∀ t, V (γ t) = V v) :
    massForm V v (deriv γ 0) = 0 := by
  have hgrad : fderiv ℝ V v = 0 := hmin.fderiv_eq_zero
  have hconst : (fun s => fderiv ℝ V (γ s) (deriv γ s)) = fun _ : ℝ => (0 : ℝ) := by
    funext s
    have h1 : HasDerivAt (fun u => V (γ u)) (fderiv ℝ V (γ s) (deriv γ s)) s :=
      ((hV.differentiable (by norm_num) (γ s)).hasFDerivAt).comp_hasDerivAt s
        ((hγ.differentiable (by norm_num) s).hasDerivAt)
    have h2 : HasDerivAt (fun u => V (γ u)) 0 s := by
      have hfun : (fun u => V (γ u)) = fun _ : ℝ => V v := funext hinv
      rw [hfun]
      exact hasDerivAt_const s (V v)
    exact h1.unique h2
  have hd := hasDerivAt_dirDeriv V hV γ hγ 0
  rw [hγ0, hgrad] at hd
  simp only [ContinuousLinearMap.zero_apply, add_zero] at hd
  have hzero : HasDerivAt (fun s => fderiv ℝ V (γ s) (deriv γ s)) 0 0 := by
    rw [hconst]; exact hasDerivAt_const 0 (0 : ℝ)
  have hquad : massForm V v (deriv γ 0) (deriv γ 0) = 0 := hd.unique hzero
  exact clm_apply_eq_zero_of_quadratic_eq_zero (massForm_nonneg V hV hmin)
    (massForm_symm V hV v) hquad

/-- Along the orbit of a one-parameter group of linear symmetries, the velocity is
transported by the group: `γ'(s) = R s (γ'(0))`. -/
lemma deriv_orbit (R : ℝ → (E →L[ℝ] E)) (hR : ContDiff ℝ 2 (fun t => R t))
    (hgroup : ∀ s t, R (s + t) = (R s).comp (R t)) (v : E) (s : ℝ) :
    deriv (fun t => R t v) s = R s (deriv (fun t => R t v) 0) := by
  set γ : ℝ → E := fun t => R t v with hγdef
  have hγC : ContDiff ℝ 2 γ := (ContinuousLinearMap.apply ℝ E v).contDiff.comp hR
  have hshift : (fun h => γ (s + h)) = fun h => R s (γ h) := by
    funext h
    simp [hγdef, hgroup s h]
  have h1 : HasDerivAt (fun h => γ (s + h)) (deriv γ s) 0 := by
    have hs : HasDerivAt γ (deriv γ s) (s + 0) := by
      rw [add_zero]
      exact (hγC.differentiable (by norm_num) s).hasDerivAt
    exact hs.comp_const_add s 0
  have h2 : HasDerivAt (fun h => R s (γ h)) (R s (deriv γ 0)) 0 :=
    (R s).hasFDerivAt.comp_hasDerivAt 0 ((hγC.differentiable (by norm_num) 0).hasDerivAt)
  rw [hshift] at h1
  exact h1.unique h2

/-- **Goldstone's theorem.**

Let `V : E → ℝ` be a `C²` potential on a real normed space `E` (the space of field values),
invariant under a continuous (`C²`) one-parameter group of global symmetries
`R : ℝ → (E →L[ℝ] E)`, i.e. `V (R t x) = V x` for all `t` and `x`.  Let `v` be a vacuum,
i.e. a local minimum of `V`, and suppose the symmetry is *spontaneously broken* at `v`,
i.e. `v` is not invariant: `R t v ≠ v` for some `t`.

Then the mass form (Hessian) of `V` at `v` has a nontrivial kernel: there is a nonzero
direction `X` with `massForm V v X = 0`, i.e. a massless mode — a Goldstone boson. -/
theorem goldstone (V : E → ℝ) (hV : ContDiff ℝ 2 V)
    (R : ℝ → (E →L[ℝ] E)) (hR : ContDiff ℝ 2 (fun t => R t))
    (hR0 : R 0 = ContinuousLinearMap.id ℝ E)
    (hgroup : ∀ s t, R (s + t) = (R s).comp (R t))
    (hsym : ∀ (t : ℝ) (x : E), V (R t x) = V x)
    (v : E) (hmin : IsLocalMin V v) (hbroken : ∃ t : ℝ, R t v ≠ v) :
    ∃ X : E, X ≠ 0 ∧ massForm V v X = 0 := by
  set γ : ℝ → E := fun t => R t v with hγdef
  have hγC : ContDiff ℝ 2 γ := (ContinuousLinearMap.apply ℝ E v).contDiff.comp hR
  have hγ0 : γ 0 = v := by simp [hγdef, hR0]
  refine ⟨deriv γ 0, ?_, ?_⟩
  · -- the symmetry being broken forces a nonzero generator direction
    intro hX
    obtain ⟨t, ht⟩ := hbroken
    apply ht
    have hzero : ∀ s : ℝ, deriv γ s = 0 := by
      intro s
      rw [deriv_orbit R hR hgroup v s, hX, map_zero]
    have hconst := is_const_of_deriv_eq_zero (hγC.differentiable (by norm_num)) hzero t 0
    rw [hγ0] at hconst
    exact hconst
  · exact goldstone_of_curve V hV hmin γ hγC hγ0 (fun t => hsym t v)

/-! ## A concrete instance: the Mexican-hat (Higgs) potential

The hypotheses of `Phys.goldstone` are satisfiable: we exhibit the standard example of a
complex field with potential `V z = (|z|² - 1)²`, invariant under the global phase rotations
`z ↦ e^{it} z`, with vacuum `z = 1`, which is not phase invariant.  Goldstone's theorem then
produces a massless mode (the phase direction). -/

/-- The Mexican-hat potential `V z = (‖z‖² - 1)²` on the complex field values. -/
noncomputable def mexicanHatPotential : ℂ → ℝ := fun z => (‖z‖ ^ 2 - 1) ^ 2

/-- The global `U(1)` phase symmetry `z ↦ e^{i t} z`, as `ℝ`-linear maps of `ℂ`. -/
noncomputable def phaseRotation : ℝ → (ℂ →L[ℝ] ℂ) :=
  fun t => Complex.exp (Complex.ofRealCLM t * Complex.I) • ContinuousLinearMap.id ℝ ℂ

lemma contDiff_mexicanHatPotential : ContDiff ℝ 2 mexicanHatPotential := by
  have h : ContDiff ℝ 2 (fun z : ℂ => ‖z‖ ^ 2) := by
    simpa using (contDiff_norm_sq ℝ (E := ℂ) (n := 2))
  unfold mexicanHatPotential
  fun_prop

lemma contDiff_phaseRotation : ContDiff ℝ 2 (fun t => phaseRotation t) := by
  unfold phaseRotation; fun_prop

lemma phaseRotation_zero : phaseRotation 0 = ContinuousLinearMap.id ℝ ℂ := by
  simp [phaseRotation]

lemma phaseRotation_add (s t : ℝ) :
    phaseRotation (s + t) = (phaseRotation s).comp (phaseRotation t) := by
  ext z
  simp [phaseRotation, Complex.exp_add, add_mul]
  ring

lemma mexicanHatPotential_invariant (t : ℝ) (x : ℂ) :
    mexicanHatPotential (phaseRotation t x) = mexicanHatPotential x := by
  have hx : phaseRotation t x = Complex.exp (t * Complex.I) * x := by simp [phaseRotation]
  rw [mexicanHatPotential, mexicanHatPotential, hx, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul]

lemma isLocalMin_mexicanHatPotential : IsLocalMin mexicanHatPotential 1 := by
  refine Filter.Eventually.of_forall (fun z => ?_)
  simp only [mexicanHatPotential, norm_one, one_pow, sub_self, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow]
  positivity

lemma phaseRotation_pi_ne : phaseRotation Real.pi 1 ≠ 1 := by
  have h : phaseRotation Real.pi 1 = Complex.exp (Real.pi * Complex.I) := by
    simp [phaseRotation]
  rw [h, Complex.exp_pi_mul_I]
  norm_num

/-- **Goldstone's theorem for the Mexican-hat potential.**  The `U(1)` phase symmetry of
`V z = (‖z‖² - 1)²` is spontaneously broken at the vacuum `z = 1`, and consequently the mass
form at that vacuum has a nonzero kernel vector: a massless (Goldstone) mode.  This also
shows that the hypotheses of `Phys.goldstone` are satisfiable. -/
theorem goldstone_mexicanHat :
    ∃ X : ℂ, X ≠ 0 ∧ massForm mexicanHatPotential 1 X = 0 :=
  goldstone mexicanHatPotential contDiff_mexicanHatPotential phaseRotation
    contDiff_phaseRotation phaseRotation_zero phaseRotation_add
    mexicanHatPotential_invariant 1 isLocalMin_mexicanHatPotential
    ⟨Real.pi, phaseRotation_pi_ne⟩

end Phys

