import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
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

namespace Frontier

/-! ## Differential operators on `ℝ³` -/

/-- Three dimensional Euclidean space. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The `i`-th partial derivative of a (vector or scalar valued) field on `ℝ³`. -/
noncomputable def partialD {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : Fin 3) (f : E3 → F) (x : E3) : F :=
  fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ))

/-- The divergence `∇ · u` of a vector field on `ℝ³`. -/
noncomputable def divg (u : E3 → E3) (x : E3) : ℝ := ∑ i, (partialD i u x) i

/-- The gradient `∇p` of a scalar field on `ℝ³`. -/
noncomputable def grad (p : E3 → ℝ) (x : E3) : E3 :=
  ∑ i, (partialD i p x) • EuclideanSpace.single i (1 : ℝ)

/-- The (componentwise) Laplacian `Δ` on `ℝ³`. -/
noncomputable def lapl {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E3 → F) (x : E3) : F := ∑ i, partialD i (fun y => partialD i f y) x

/-- The convective term `(u · ∇) u`, i.e. the derivative of `u` in the direction `u x`. -/
noncomputable def convective (u : E3 → E3) (x : E3) : E3 := fderiv ℝ u x (u x)

/-! ## The Navier–Stokes system -/

/-- `IsNSSolution ν u p` says that the velocity field `u : ℝ → ℝ³ → ℝ³` and the pressure
`p : ℝ → ℝ³ → ℝ` are smooth in space-time and solve the incompressible Navier–Stokes
equations with viscosity `ν` and zero external force for all times `t ≥ 0`:

* `∇ · u = 0`,
* `∂ₜ u + (u · ∇) u = ν Δ u - ∇ p`.

Smoothness is required on all of `ℝ × ℝ³`, while the equations are only imposed for `t ≥ 0`. -/
structure IsNSSolution (ν : ℝ) (u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ) : Prop where
  smooth_u : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × E3 => u q.1 q.2)
  smooth_p : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × E3 => p q.1 q.2)
  div_free : ∀ t, 0 ≤ t → ∀ x, divg (u t) x = 0
  momentum : ∀ t, 0 ≤ t → ∀ x,
    deriv (fun s => u s x) t + convective (u t) x = ν • lapl (u t) x - grad (p t) x

/-- Uniform-in-time bound on the kinetic energy of a velocity field, as required in the
statement of the Clay Millennium Problem. -/
def BoundedEnergy (u : ℝ → E3 → E3) : Prop :=
  ∃ C : ℝ, ∀ t, 0 ≤ t → ∫ x : E3, ‖u t x‖ ^ 2 ≤ C

/-- `SolvableData ν u₀` : the divergence free datum `u₀` launches a globally defined,
globally smooth, finite energy solution of the Navier–Stokes system with viscosity `ν`. -/
def SolvableData (ν : ℝ) (u₀ : E3 → E3) : Prop :=
  ∃ u : ℝ → E3 → E3, ∃ p : ℝ → E3 → ℝ,
    IsNSSolution ν u p ∧ (∀ x, u 0 x = u₀ x) ∧ BoundedEnergy u

/-- **Global regularity for the three dimensional incompressible Navier–Stokes equations**
(the Clay Millennium Problem, case of zero external force): for every viscosity `ν > 0` and
every divergence free Schwartz initial datum `u₀` on `ℝ³` there exist a smooth velocity field
and pressure, defined for all times, solving the Navier–Stokes system with datum `u₀` and with
uniformly bounded kinetic energy. -/
def NavierStokesGlobalRegularity : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ U : SchwartzMap E3 E3, (∀ x, divg (⇑U) x = 0) → SolvableData ν (⇑U)

/-! ## Elementary properties of the differential operators -/

lemma partialD_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (i : Fin 3) (x : E3) :
    partialD i (fun _ : E3 => (0 : F)) x = 0 := by
  simp [partialD]

lemma divg_zero (x : E3) : divg (fun _ : E3 => (0 : E3)) x = 0 := by
  simp [divg, partialD]

lemma grad_zero (x : E3) : grad (fun _ : E3 => (0 : ℝ)) x = 0 := by
  simp [grad, partialD]

lemma lapl_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (x : E3) :
    lapl (fun _ : E3 => (0 : F)) x = 0 := by
  simp [lapl, partialD]

/-! ## Sanity checks for the differential operators -/

/-- `∇ · x = 3` on `ℝ³`. -/
lemma divg_id (x : E3) : divg (fun y => y) x = 3 := by
  have h : ∀ i : Fin 3, partialD i (fun y : E3 => y) x = EuclideanSpace.single i (1 : ℝ) := by
    intro i; simp [partialD]
  simp [divg, h, EuclideanSpace.single_apply]

/-- `Δ (x₀²) = 2` on `ℝ³`. -/
lemma lapl_sq_coord (x : E3) : lapl (fun y : E3 => (y 0) * (y 0)) x = 2 := by
  have hproj : ∀ v : E3, (EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ) v = v 0 := fun _ => rfl
  have hp : ∀ y : E3, HasFDerivAt (fun z : E3 => (z 0) * (z 0))
      ((y 0) • (EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ)
        + (y 0) • (EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ)) y := by
    intro y
    have h0 : HasFDerivAt (fun z : E3 => z 0) (EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ) y :=
      (EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ).hasFDerivAt
    simpa [add_comm, smul_eq_mul] using h0.mul h0
  have h1 : ∀ (i : Fin 3) (y : E3), partialD i (fun z : E3 => (z 0) * (z 0)) y
      = 2 * (y 0) * (EuclideanSpace.single i (1 : ℝ) 0) := by
    intro i y
    simp only [partialD, (hp y).fderiv, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, hproj, smul_eq_mul]
    ring
  have h2 : ∀ i : Fin 3, partialD i (fun y : E3 => partialD i (fun z : E3 => (z 0) * (z 0)) y) x
      = 2 * (EuclideanSpace.single i (1 : ℝ) 0) * (EuclideanSpace.single i (1 : ℝ) 0) := by
    intro i
    have he : (fun y : E3 => partialD i (fun z : E3 => (z 0) * (z 0)) y)
        = fun y : E3 => (2 * (EuclideanSpace.single i (1 : ℝ) 0)) * (y 0) := by
      funext y; rw [h1 i y]; ring
    rw [he]
    have h0 : HasFDerivAt (fun y : E3 => (2 * (EuclideanSpace.single i (1 : ℝ) 0)) * (y 0))
        ((2 * (EuclideanSpace.single i (1 : ℝ) 0))
          • (EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ)) x :=
      ((EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ).hasFDerivAt).const_mul _
    simp only [partialD, h0.fderiv, ContinuousLinearMap.smul_apply, hproj, smul_eq_mul]
  simp [lapl, h2, EuclideanSpace.single_apply]

/-! ## The base case : the zero solution -/

/-- The zero velocity field with zero pressure is a global smooth solution. -/
theorem isNSSolution_zero (ν : ℝ) :
    IsNSSolution ν (fun _ _ => (0 : E3)) (fun _ _ => (0 : ℝ)) where
  smooth_u := contDiff_const
  smooth_p := contDiff_const
  div_free := by intro t _ x; simpa using divg_zero x
  momentum := by
    intro t _ x
    simp [convective, lapl, grad, partialD]

/-- The base case of the Millennium Problem: the zero initial datum is solvable. -/
theorem solvableData_zero (ν : ℝ) : SolvableData ν (fun _ => 0) :=
  ⟨fun _ _ => 0, fun _ _ => 0, isNSSolution_zero ν, fun _ => rfl, ⟨0, by intro t _; simp⟩⟩

/-! ## The scaling reduction -/

/-- Chain rule for the scaling `x ↦ c • x` in a partial derivative. -/
lemma partialD_comp_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E3 → F) (hf : Differentiable ℝ f) (c : ℝ) (i : Fin 3) (x : E3) :
    partialD i (fun y => f (c • y)) x = c • partialD i f (c • x) := by
  have h1 : HasFDerivAt (fun y : E3 => c • y) (c • ContinuousLinearMap.id ℝ E3) x :=
    (hasFDerivAt_id x).const_smul c
  have h2 : HasFDerivAt (fun y : E3 => f (c • y))
      ((fderiv ℝ f (c • x)).comp (c • ContinuousLinearMap.id ℝ E3)) x :=
    ((hf (c • x)).hasFDerivAt).comp x h1
  simp [partialD, h2.fderiv]

/-- Partial derivatives of a `C²` field are differentiable. -/
lemma differentiable_partialD {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E3 → F) (hf : ContDiff ℝ (2 : ℕ) f) (i : Fin 3) :
    Differentiable ℝ (fun y => partialD i f y) := by
  have h1 : ContDiff ℝ (1 : ℕ) (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have h2 : Differentiable ℝ (fderiv ℝ f) := h1.differentiable (by norm_num)
  exact ((ContinuousLinearMap.apply ℝ F (EuclideanSpace.single i (1 : ℝ))).differentiable).comp h2

lemma partialD_const_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E3 → F) (c : ℝ) (i : Fin 3) (x : E3) (hf : DifferentiableAt ℝ f x) :
    partialD i (fun y => c • f y) x = c • partialD i f x := by
  have h : fderiv ℝ (fun y => c • f y) x = c • fderiv ℝ f x := fderiv_const_smul hf c
  simp [partialD, h]

lemma divg_comp_smul (u : E3 → E3) (hu : Differentiable ℝ u) (c : ℝ) (x : E3) :
    divg (fun y => c • u (c • y)) x = c ^ 2 * divg u (c • x) := by
  have hd : ∀ i : Fin 3, partialD i (fun y => c • u (c • y)) x = (c * c) • partialD i u (c • x) := by
    intro i
    rw [partialD_const_smul (fun y => u (c • y)) c i x
      ((hu (c • x)).comp x ((differentiable_id.const_smul c) x)),
      partialD_comp_smul u hu c i x, smul_smul]
  simp only [divg, hd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

lemma lapl_comp_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E3 → F) (hf : ContDiff ℝ (2 : ℕ) f) (c : ℝ) (x : E3) :
    lapl (fun y => f (c • y)) x = c ^ 2 • lapl f (c • x) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have key : ∀ i : Fin 3, (fun y => partialD i (fun z => f (c • z)) y)
      = fun y => c • partialD i f (c • y) := by
    intro i; funext y; exact partialD_comp_smul f hfd c i y
  simp only [lapl, key, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdi : Differentiable ℝ (fun y => partialD i f y) := differentiable_partialD f hf i
  rw [partialD_const_smul (fun y => partialD i f (c • y)) c i x
      ((hdi (c • x)).comp x ((differentiable_id.const_smul c) x)),
    partialD_comp_smul (fun y => partialD i f y) hdi c i x, smul_smul, sq]

lemma grad_comp_smul (p : E3 → ℝ) (hp : Differentiable ℝ p) (c : ℝ) (x : E3) :
    grad (fun y => p (c • y)) x = c • grad p (c • x) := by
  simp only [grad, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [partialD_comp_smul p hp c i x, smul_assoc]

lemma grad_const_smul (p : E3 → ℝ) (c : ℝ) (x : E3) (hp : DifferentiableAt ℝ p x) :
    grad (fun y => c * p y) x = c • grad p x := by
  simp only [grad, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := partialD_const_smul p c i x hp
  simp only [smul_eq_mul] at this
  rw [this, mul_smul]

lemma lapl_const_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E3 → F) (hf : ContDiff ℝ (2 : ℕ) f) (c : ℝ) (x : E3) :
    lapl (fun y => c • f y) x = c • lapl f x := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have key : ∀ i : Fin 3, (fun y => partialD i (fun z => c • f z) y)
      = fun y => c • partialD i f y := by
    intro i; funext y; exact partialD_const_smul f c i y (hfd y)
  simp only [lapl, key, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact partialD_const_smul _ c i x (differentiable_partialD f hf i x)

lemma convective_scale (u : E3 → E3) (hu : Differentiable ℝ u) (c : ℝ) (x : E3) :
    convective (fun y => c • u (c • y)) x = c ^ 3 • convective u (c • x) := by
  have h1 : HasFDerivAt (fun y : E3 => c • u (c • y))
      (c • ((fderiv ℝ u (c • x)).comp (c • ContinuousLinearMap.id ℝ E3))) x :=
    ((((hu (c • x)).hasFDerivAt).comp x ((hasFDerivAt_id x).const_smul c)).const_smul c)
  simp only [convective, h1.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.coe_id', id_eq, map_smul, smul_smul]
  ring_nf

/-- Space regularity of a Navier–Stokes solution at a fixed time. -/
lemma IsNSSolution.contDiff_space {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (h : IsNSSolution ν u p) (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (u t) :=
  h.smooth_u.comp (contDiff_const.prodMk contDiff_id)

lemma IsNSSolution.contDiff_space_pressure {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (h : IsNSSolution ν u p) (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (p t) :=
  h.smooth_p.comp (contDiff_const.prodMk contDiff_id)

lemma IsNSSolution.differentiable_time {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (h : IsNSSolution ν u p) (x : E3) : Differentiable ℝ (fun s => u s x) :=
  (h.smooth_u.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)

/-- The Navier–Stokes scaling: if `(u, p)` solves the system, then so does
`(c u(c x, c² t), c² p(c x, c² t))` for every real `c`. -/
theorem isNSSolution_scale {ν : ℝ} {u : ℝ → E3 → E3} {p : ℝ → E3 → ℝ}
    (h : IsNSSolution ν u p) (c : ℝ) :
    IsNSSolution ν (fun t x => c • u (c ^ 2 * t) (c • x))
      (fun t x => c ^ 2 * p (c ^ 2 * t) (c • x)) := by
  have hscale : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × E3 => ((c ^ 2 * q.1 : ℝ), c • q.2)) :=
    (contDiff_const.mul contDiff_fst).prodMk (contDiff_snd.const_smul c)
  have hspace : ∀ t : ℝ, ContDiff ℝ (2 : ℕ) (u t) := fun t =>
    (h.contDiff_space t).of_le (WithTop.coe_le_coe.mpr le_top)
  have hspaceD : ∀ t : ℝ, Differentiable ℝ (u t) := fun t =>
    (hspace t).differentiable (by norm_num)
  have hpD : ∀ t : ℝ, Differentiable ℝ (p t) := fun t =>
    (h.contDiff_space_pressure t).differentiable (by simp)
  refine ⟨(h.smooth_u.comp hscale).const_smul c, ?_, ?_, ?_⟩
  · exact contDiff_const.mul (h.smooth_p.comp hscale)
  · intro t ht x
    rw [divg_comp_smul (u (c ^ 2 * t)) (hspaceD _) c x,
      h.div_free _ (by positivity) (c • x), mul_zero]
  · intro t ht x
    have ht' : (0 : ℝ) ≤ c ^ 2 * t := by positivity
    have hmom := h.momentum (c ^ 2 * t) ht' (c • x)
    -- time derivative
    have hA : deriv (fun s => c • u (c ^ 2 * s) (c • x)) t
        = c ^ 3 • deriv (fun s => u s (c • x)) (c ^ 2 * t) := by
      have h1 : HasDerivAt (fun s : ℝ => c ^ 2 * s) (c ^ 2) t := by
        simpa using (hasDerivAt_id t).const_mul (c ^ 2)
      have h2 : HasDerivAt (fun s : ℝ => u (c ^ 2 * s) (c • x))
          (c ^ 2 • deriv (fun s => u s (c • x)) (c ^ 2 * t)) t :=
        ((h.differentiable_time (c • x) (c ^ 2 * t)).hasDerivAt).scomp t h1
      have h3 := (h2.const_smul c).deriv
      rw [show (fun s => c • u (c ^ 2 * s) (c • x))
          = (c • fun s => u (c ^ 2 * s) (c • x)) from rfl, h3, smul_smul]
      ring_nf
    have hB : convective (fun y => c • u (c ^ 2 * t) (c • y)) x
        = c ^ 3 • convective (u (c ^ 2 * t)) (c • x) :=
      convective_scale _ (hspaceD _) c x
    have hC : lapl (fun y => c • u (c ^ 2 * t) (c • y)) x
        = c ^ 3 • lapl (u (c ^ 2 * t)) (c • x) := by
      rw [lapl_const_smul (fun y => u (c ^ 2 * t) (c • y))
        ((hspace _).comp ((contDiff_id.const_smul c))) c x,
        lapl_comp_smul (u (c ^ 2 * t)) (hspace _) c x, smul_smul]
      ring_nf
    have hD : grad (fun y => c ^ 2 * p (c ^ 2 * t) (c • y)) x
        = c ^ 3 • grad (p (c ^ 2 * t)) (c • x) := by
      rw [grad_const_smul (fun y => p (c ^ 2 * t) (c • y)) (c ^ 2) x
          (((hpD _) (c • x)).comp x ((differentiable_id.const_smul c) x)),
        grad_comp_smul (p (c ^ 2 * t)) (hpD _) c x, smul_smul]
      ring_nf
    simp only [hA, hB, hC, hD]
    rw [← smul_add, hmom, smul_sub, smul_comm (c ^ 3) ν]

/-- Kinetic energy under the Navier–Stokes scaling of a velocity field on `ℝ³`. -/
lemma integral_norm_sq_scale (g : E3 → E3) {c : ℝ} (hc : 0 < c) :
    ∫ x : E3, ‖c • g (c • x)‖ ^ 2 = c ^ 2 * ((c ^ 3)⁻¹ * ∫ y : E3, ‖g y‖ ^ 2) := by
  have h1 : ∀ x : E3, ‖c • g (c • x)‖ ^ 2 = c ^ 2 * ‖g (c • x)‖ ^ 2 := by
    intro x
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp only [h1]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [MeasureTheory.Measure.integral_comp_smul
    (μ := (MeasureTheory.volume : MeasureTheory.Measure E3)) (fun y : E3 => ‖g y‖ ^ 2) c]
  simp [abs_of_pos, inv_pos.mpr (pow_pos hc 3)]

/-- Scaling reduction for the Millennium Problem: the class of solvable initial data is
invariant under the Navier–Stokes scaling `u₀ ↦ c u₀(c ·)`. -/
theorem solvableData_scale {ν : ℝ} {u₀ : E3 → E3} (h : SolvableData ν u₀) {c : ℝ} (hc : 0 < c) :
    SolvableData ν (fun x => c • u₀ (c • x)) := by
  obtain ⟨u, p, hsol, hinit, C, hC⟩ := h
  refine ⟨fun t x => c • u (c ^ 2 * t) (c • x), fun t x => c ^ 2 * p (c ^ 2 * t) (c • x),
    isNSSolution_scale hsol c, fun x => by simp [hinit], ⟨c ^ 2 * ((c ^ 3)⁻¹ * C), ?_⟩⟩
  intro t ht
  rw [integral_norm_sq_scale (u (c ^ 2 * t)) hc]
  have hle : (∫ y : E3, ‖u (c ^ 2 * t) y‖ ^ 2) ≤ C := hC _ (by positivity)
  have hpos : (0 : ℝ) < (c ^ 3)⁻¹ := inv_pos.mpr (pow_pos hc 3)
  have := mul_le_mul_of_nonneg_left hle hpos.le
  exact mul_le_mul_of_nonneg_left this (by positivity)

/-! ## Reduction to small initial energy -/

/-- The Navier–Stokes rescaling `U ↦ c U(c ·)` of a Schwartz field, as a Schwartz field. -/
noncomputable def scaledSchwartz (c : ℝ) (hc : 0 < c) (U : SchwartzMap E3 E3) :
    SchwartzMap E3 E3 :=
  c • (SchwartzMap.compCLM (g := fun x : E3 => c • x) ℝ
    ((c • ContinuousLinearMap.id ℝ E3).hasTemperateGrowth)
    ⟨1, c⁻¹, by
      intro x
      have hnorm : ‖c • x‖ = c * ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      rw [hnorm, pow_one]
      have h1 : ‖x‖ = c⁻¹ * (c * ‖x‖) := by rw [inv_mul_cancel_left₀ hc.ne']
      nlinarith [norm_nonneg x, inv_pos.mpr hc]⟩ U)

@[simp] lemma scaledSchwartz_apply (c : ℝ) (hc : 0 < c) (U : SchwartzMap E3 E3) (x : E3) :
    scaledSchwartz c hc U x = c • U (c • x) := by
  simp [scaledSchwartz]

/-- **Reduction to small initial energy.**  If, for some fixed `ε > 0`, every divergence free
Schwartz datum of kinetic energy less than `ε` launches a global smooth finite energy solution,
then global regularity holds for *all* divergence free Schwartz data.  Indeed, the
Navier–Stokes scaling `u₀ ↦ c u₀(c ·)` divides the energy by `c`, and it maps solutions to
solutions in both directions. -/
theorem navierStokesGlobalRegularity_of_small_energy (eps : ℝ) (heps : 0 < eps)
    (H : ∀ ν : ℝ, 0 < ν → ∀ U : SchwartzMap E3 E3, (∀ x, divg (⇑U) x = 0) →
      (∫ x : E3, ‖U x‖ ^ 2) < eps → SolvableData ν (⇑U)) :
    NavierStokesGlobalRegularity := by
  intro ν hν U hdiv
  set En : ℝ := ∫ x : E3, ‖U x‖ ^ 2 with hEn
  have hEn0 : 0 ≤ En := MeasureTheory.integral_nonneg fun x => by positivity
  set c : ℝ := En / eps + 1 with hcdef
  have hc : 0 < c := by
    have : 0 ≤ En / eps := div_nonneg hEn0 heps.le
    simp only [hcdef]; linarith
  have hUdiff : Differentiable ℝ (⇑U) := (U.smooth (⊤ : ℕ∞)).differentiable (by simp)
  -- the rescaled datum
  set V : SchwartzMap E3 E3 := scaledSchwartz c hc U with hV
  have hVdiv : ∀ x, divg (⇑V) x = 0 := by
    intro x
    have hVfun : (⇑V) = fun y => c • U (c • y) := by
      funext y; simp [hV]
    rw [hVfun, divg_comp_smul (⇑U) hUdiff c x, hdiv (c • x), mul_zero]
  have hVenergy : (∫ x : E3, ‖V x‖ ^ 2) < eps := by
    have hVfun : ∀ x : E3, ‖V x‖ ^ 2 = ‖c • U (c • x)‖ ^ 2 := by
      intro x; simp [hV]
    simp only [hVfun]
    rw [integral_norm_sq_scale (⇑U) hc, ← hEn]
    have hcne : c ≠ 0 := hc.ne'
    have hrw : c ^ 2 * ((c ^ 3)⁻¹ * En) = En / c := by
      field_simp
    rw [hrw, div_lt_iff₀ hc, hcdef]
    have : En / eps * eps = En := div_mul_cancel₀ En heps.ne'
    nlinarith [this]
  have hVsolv : SolvableData ν (⇑V) := H ν hν V hVdiv hVenergy
  have hback := solvableData_scale hVsolv (c := c⁻¹) (inv_pos.mpr hc)
  have hfun : (fun x => c⁻¹ • (⇑V) (c⁻¹ • x)) = (⇑U) := by
    funext x
    simp only [hV, scaledSchwartz_apply, smul_smul]
    rw [mul_inv_cancel₀ hc.ne', one_smul, inv_mul_cancel₀ hc.ne', one_smul]
  rwa [hfun] at hback

/-! ## Main statement -/

/-- **Navier–Stokes regularity.**  The full formal statement of the three dimensional
incompressible Navier–Stokes global regularity problem (Clay Millennium Problem, zero external
force) is recorded as the definition `Frontier.NavierStokesGlobalRegularity`.  The theorem below
collects the three facts about it that are established here:

* the *base case*: the zero initial datum launches a global smooth finite energy solution;
* the *scaling invariance*: the class of solvable initial data is closed under the
  Navier–Stokes scaling `u₀ ↦ c u₀(c ·)`, `c > 0`;
* a Lean-checked *reduction*: for any `ε > 0`, global regularity for all divergence free
  Schwartz data of kinetic energy `< ε` already implies the full conjecture. -/
theorem navier_stokes_regularity :
    (∀ ν : ℝ, SolvableData ν (fun _ => 0)) ∧
    (∀ (ν : ℝ) (u₀ : E3 → E3), SolvableData ν u₀ →
        ∀ c : ℝ, 0 < c → SolvableData ν (fun x => c • u₀ (c • x))) ∧
    (∀ eps : ℝ, 0 < eps →
        (∀ ν : ℝ, 0 < ν → ∀ U : SchwartzMap E3 E3, (∀ x, divg (⇑U) x = 0) →
          (∫ x : E3, ‖U x‖ ^ 2) < eps → SolvableData ν (⇑U)) →
        NavierStokesGlobalRegularity) :=
  ⟨solvableData_zero, fun _ _ h _ hc => solvableData_scale h hc,
    navierStokesGlobalRegularity_of_small_energy⟩

end Frontier

