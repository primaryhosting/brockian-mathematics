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
# Deficiency Represents ODE Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.deficiencyRepresentsODE_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

open MeasureTheory Set

namespace Brockian.Weyl.DeficiencyODE

/-- `IsWeakSolution q z u v` says that the pair `(u, v)` is a *weak* solution of the
deficiency equation `u'' = (q - z) * u` of the Sturm–Liouville expression
`L u = -u'' + q u`, in the sense that `u` and `v` are merely continuous and satisfy the
integrated (Volterra) form of the system `u' = v`, `v' = (q - z) u`.

No differentiability whatsoever is assumed: this is the "weak regularity" hypothesis. -/
structure IsWeakSolution (q : ℝ → ℂ) (z : ℂ) (u v : ℝ → ℂ) : Prop where
  continuous_u : Continuous u
  continuous_v : Continuous v
  integral_u : ∀ t : ℝ, u t = u 0 + ∫ s in (0:ℝ)..t, v s
  integral_v : ∀ t : ℝ, v t = v 0 + ∫ s in (0:ℝ)..t, (q s - z) * u s

variable {q : ℝ → ℂ} {z : ℂ} {u v : ℝ → ℂ}

/-- A weak solution is automatically differentiable, with derivative the second component. -/
theorem IsWeakSolution.hasDerivAt_left (h : IsWeakSolution q z u v) (t : ℝ) :
    HasDerivAt u (v t) t := by
  have hfun : u = fun x : ℝ => u 0 + ∫ s in (0:ℝ)..x, v s := funext h.integral_u
  rw [hfun]
  exact ((h.continuous_v.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add (u 0)

/-- The second component of a weak solution is automatically differentiable, with
derivative `(q - z) u`; here continuity of `q` is used. -/
theorem IsWeakSolution.hasDerivAt_right (hq : Continuous q) (h : IsWeakSolution q z u v)
    (t : ℝ) : HasDerivAt v ((q t - z) * u t) t := by
  have hcont : Continuous fun s : ℝ => (q s - z) * u s :=
    ((hq.sub continuous_const).mul h.continuous_u)
  have hfun : v = fun x : ℝ => v 0 + ∫ s in (0:ℝ)..x, (q s - z) * u s := funext h.integral_v
  rw [hfun]
  exact ((hcont.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add (v 0)

theorem IsWeakSolution.deriv_eq (h : IsWeakSolution q z u v) : deriv u = v :=
  funext fun t => (h.hasDerivAt_left t).deriv

/-- Derivative of the complex exponential along the real line. -/
theorem hasDerivAt_cexp_ofReal (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (s : ℂ)) (Complex.exp (t : ℂ)) t :=
  (Complex.hasDerivAt_exp ((t : ℂ))).comp_ofReal

/-- The notion of weak solution is non-vacuous: for `q = 0` and `z = -1` the exponential
is a nonzero weak solution of `u'' = (q - z) u`, i.e. of `u'' = u`. -/
theorem isWeakSolution_exp :
    IsWeakSolution (fun _ => 0) (-1) (fun s : ℝ => Complex.exp (s : ℂ))
      (fun s : ℝ => Complex.exp (s : ℂ)) where
  continuous_u := Complex.continuous_exp.comp Complex.continuous_ofReal
  continuous_v := Complex.continuous_exp.comp Complex.continuous_ofReal
  integral_u t := by
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => Complex.exp (s : ℂ)) (f' := fun s : ℝ => Complex.exp (s : ℂ))
      (a := 0) (b := t) (fun x _ => hasDerivAt_cexp_ofReal x)
      ((Complex.continuous_exp.comp Complex.continuous_ofReal).intervalIntegrable 0 t)
    simp only [Complex.ofReal_zero, Complex.exp_zero] at hint ⊢
    rw [hint]; ring
  integral_v t := by
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => Complex.exp (s : ℂ)) (f' := fun s : ℝ => Complex.exp (s : ℂ))
      (a := 0) (b := t) (fun x _ => hasDerivAt_cexp_ofReal x)
      ((Complex.continuous_exp.comp Complex.continuous_ofReal).intervalIntegrable 0 t)
    simp only [Complex.ofReal_zero, Complex.exp_zero, zero_sub, neg_neg, one_mul] at hint ⊢
    rw [hint]; ring

theorem cexp_ofReal_ne_zero : (fun s : ℝ => Complex.exp (s : ℂ)) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp at h0

/-- On any bounded interval the vector field `y ↦ (y₂, (q t - z) y₁)` of the deficiency
equation is uniformly Lipschitz. -/
theorem exists_lipschitz_vectorField (hq : Continuous q) (z : ℂ) (T : ℝ) :
    ∃ K : NNReal, ∀ t ∈ Set.Ioo (-T) T,
      LipschitzOnWith K (fun y : ℂ × ℂ => (y.2, (q t - z) * y.1)) Set.univ := by
  rcases le_or_gt T (-T) with hT | hT
  · exact ⟨0, fun t ht => absurd (ht.1.trans ht.2) (by simpa using hT.not_gt)⟩
  have hne : (Set.Icc (-T) T).Nonempty := ⟨-T, le_refl _, le_of_lt hT⟩
  obtain ⟨s₀, hs₀, hmax⟩ := isCompact_Icc.exists_isMaxOn hne
    (by fun_prop : ContinuousOn (fun s : ℝ => ‖q s - z‖) (Set.Icc (-T) T))
  refine ⟨⟨max 1 ‖q s₀ - z‖, le_trans zero_le_one (le_max_left _ _)⟩, ?_⟩
  intro t ht
  apply LipschitzOnWith.of_dist_le_mul
  intro x _ y _
  have hqt : ‖q t - z‖ ≤ max 1 ‖q s₀ - z‖ :=
    le_trans (hmax ⟨le_of_lt ht.1, le_of_lt ht.2⟩) (le_max_right _ _)
  rw [Prod.dist_eq, Prod.dist_eq]
  apply max_le
  · calc dist x.2 y.2 ≤ max (dist x.1 y.1) (dist x.2 y.2) := le_max_right _ _
      _ ≤ (max 1 ‖q s₀ - z‖) * max (dist x.1 y.1) (dist x.2 y.2) := by
          nlinarith [le_max_left (dist x.1 y.1) (dist x.2 y.2), dist_nonneg (x := x.1) (y := y.1),
            dist_nonneg (x := x.2) (y := y.2), le_max_left (1:ℝ) ‖q s₀ - z‖]
  · have heq : dist ((q t - z) * x.1) ((q t - z) * y.1) = ‖q t - z‖ * dist x.1 y.1 := by
      simp [dist_eq_norm, ← mul_sub]
    rw [heq]
    have h1 : dist x.1 y.1 ≤ max (dist x.1 y.1) (dist x.2 y.2) := le_max_left _ _
    have h2 := dist_nonneg (x := x.1) (y := y.1)
    calc ‖q t - z‖ * dist x.1 y.1 ≤ (max 1 ‖q s₀ - z‖) * dist x.1 y.1 :=
          mul_le_mul_of_nonneg_right hqt h2
      _ ≤ (max 1 ‖q s₀ - z‖) * max (dist x.1 y.1) (dist x.2 y.2) :=
          mul_le_mul_of_nonneg_left h1 (le_trans zero_le_one (le_max_left _ _))

/-- Uniqueness for the initial value problem in the weak formulation. -/
theorem IsWeakSolution.eq_of_initial (hq : Continuous q) {u₁ v₁ u₂ v₂ : ℝ → ℂ}
    (h₁ : IsWeakSolution q z u₁ v₁) (h₂ : IsWeakSolution q z u₂ v₂)
    (hu : u₁ 0 = u₂ 0) (hv : v₁ 0 = v₂ 0) : u₁ = u₂ ∧ v₁ = v₂ := by
  have key : ∀ t : ℝ, (u₁ t, v₁ t) = (u₂ t, v₂ t) := by
    intro t
    obtain ⟨T, hT, htT⟩ : ∃ T : ℝ, 0 < T ∧ |t| < T := ⟨|t| + 1, by positivity, by linarith⟩
    obtain ⟨K, hlip⟩ := exists_lipschitz_vectorField hq z T
    have := ODE_solution_unique_of_mem_Ioo
      (v := fun t (y : ℂ × ℂ) => (y.2, (q t - z) * y.1))
      (f := fun t => (u₁ t, v₁ t)) (g := fun t => (u₂ t, v₂ t))
      (s := fun _ => Set.univ) (K := K) (t₀ := 0) hlip ⟨by linarith, hT⟩
      (fun t _ => ⟨(h₁.hasDerivAt_left t).prodMk (h₁.hasDerivAt_right hq t), trivial⟩)
      (fun t _ => ⟨(h₂.hasDerivAt_left t).prodMk (h₂.hasDerivAt_right hq t), trivial⟩)
      (by simp [hu, hv])
    exact this (by simpa [Set.mem_Ioo, abs_lt] using htT)
  exact ⟨funext fun t => congrArg Prod.fst (key t), funext fun t => congrArg Prod.snd (key t)⟩

theorem isWeakSolution_zero : IsWeakSolution q z 0 0 where
  continuous_u := continuous_const
  continuous_v := continuous_const
  integral_u := by simp
  integral_v := by simp

theorem IsWeakSolution.add (hq : Continuous q) {u₁ v₁ u₂ v₂ : ℝ → ℂ}
    (h₁ : IsWeakSolution q z u₁ v₁) (h₂ : IsWeakSolution q z u₂ v₂) :
    IsWeakSolution q z (u₁ + u₂) (v₁ + v₂) where
  continuous_u := h₁.continuous_u.add h₂.continuous_u
  continuous_v := h₁.continuous_v.add h₂.continuous_v
  integral_u := by
    intro t
    have hint : ∫ s in (0:ℝ)..t, (v₁ s + v₂ s)
        = (∫ s in (0:ℝ)..t, v₁ s) + ∫ s in (0:ℝ)..t, v₂ s :=
      intervalIntegral.integral_add (h₁.continuous_v.intervalIntegrable 0 t)
        (h₂.continuous_v.intervalIntegrable 0 t)
    simp only [Pi.add_apply]
    rw [hint, h₁.integral_u t, h₂.integral_u t]
    ring
  integral_v := by
    intro t
    have hc₁ : Continuous fun s : ℝ => (q s - z) * u₁ s :=
      (hq.sub continuous_const).mul h₁.continuous_u
    have hc₂ : Continuous fun s : ℝ => (q s - z) * u₂ s :=
      (hq.sub continuous_const).mul h₂.continuous_u
    have hint : ∫ s in (0:ℝ)..t, (q s - z) * (u₁ s + u₂ s)
        = (∫ s in (0:ℝ)..t, (q s - z) * u₁ s) + ∫ s in (0:ℝ)..t, (q s - z) * u₂ s := by
      rw [← intervalIntegral.integral_add (hc₁.intervalIntegrable 0 t)
        (hc₂.intervalIntegrable 0 t)]
      exact intervalIntegral.integral_congr fun s _ => by simp [mul_add]
    simp only [Pi.add_apply]
    rw [hint, h₁.integral_v t, h₂.integral_v t]
    ring

theorem IsWeakSolution.smul (c : ℂ) (h : IsWeakSolution q z u v) :
    IsWeakSolution q z (c • u) (c • v) where
  continuous_u := h.continuous_u.const_smul c
  continuous_v := h.continuous_v.const_smul c
  integral_u := by
    intro t
    have hint : ∫ s in (0:ℝ)..t, c * v s = c * ∫ s in (0:ℝ)..t, v s :=
      intervalIntegral.integral_const_mul c v
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hint, h.integral_u t]
    ring
  integral_v := by
    intro t
    have hint : ∫ s in (0:ℝ)..t, (q s - z) * (c * u s)
        = c * ∫ s in (0:ℝ)..t, (q s - z) * u s := by
      rw [← intervalIntegral.integral_const_mul c fun s => (q s - z) * u s]
      exact intervalIntegral.integral_congr fun s _ => by ring
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hint, h.integral_v t]
    ring

/-- The deficiency space of the Sturm–Liouville expression `L u = -u'' + q u` at the
spectral parameter `z`: the square-integrable weak solutions of `u'' = (q - z) u`. -/
def deficiencySpace (q : ℝ → ℂ) (hq : Continuous q) (z : ℂ) : Submodule ℂ (ℝ → ℂ) where
  carrier := {u : ℝ → ℂ | MemLp u 2 volume ∧ ∃ v, IsWeakSolution q z u v}
  add_mem' := by
    rintro a b ⟨ha, va, hva⟩ ⟨hb, vb, hvb⟩
    exact ⟨ha.add hb, va + vb, hva.add hq hvb⟩
  zero_mem' := ⟨MemLp.zero, 0, isWeakSolution_zero⟩
  smul_mem' := by
    rintro c a ⟨ha, va, hva⟩
    exact ⟨ha.const_smul c, c • va, hva.smul c⟩

/-- **The deficiency space is represented by the ODE, assuming only weak regularity.**

For a continuous potential `q` and any spectral parameter `z`, every element of the
deficiency space at `z` — a priori only a continuous, square-integrable solution of the
*integrated* form of the equation — is a genuine classical solution of the differential
equation `u'' = (q - z) u`; such a solution is determined by its Cauchy data `(u 0, u' 0)`;
and consequently the deficiency space has dimension at most `2`. -/
theorem deficiencyRepresentsODE_of_weakRegularity (q : ℝ → ℂ) (hq : Continuous q) (z : ℂ) :
    (∀ u ∈ deficiencySpace q hq z, ∀ t : ℝ,
        HasDerivAt u (deriv u t) t ∧ HasDerivAt (deriv u) ((q t - z) * u t) t) ∧
    (∀ u ∈ deficiencySpace q hq z, u 0 = 0 → deriv u 0 = 0 → u = 0) ∧
    Module.rank ℂ (deficiencySpace q hq z) ≤ 2 := by
  have hderiv : ∀ u ∈ deficiencySpace q hq z, ∀ t : ℝ,
      HasDerivAt u (deriv u t) t ∧ HasDerivAt (deriv u) ((q t - z) * u t) t := by
    rintro u ⟨-, v, hws⟩ t
    rw [hws.deriv_eq]
    exact ⟨hws.hasDerivAt_left t, hws.hasDerivAt_right hq t⟩
  have huniq : ∀ u ∈ deficiencySpace q hq z, u 0 = 0 → deriv u 0 = 0 → u = 0 := by
    rintro u ⟨-, v, hws⟩ h0 h0'
    have hv0 : v 0 = 0 := by rw [← hws.deriv_eq]; exact h0'
    exact (hws.eq_of_initial hq isWeakSolution_zero (by simpa using h0) (by simpa using hv0)).1
  refine ⟨hderiv, huniq, ?_⟩
  -- the Cauchy-data map is linear and injective on the deficiency space
  have hderiv_add : ∀ (a b : deficiencySpace q hq z),
      deriv ((a : ℝ → ℂ) + (b : ℝ → ℂ)) 0 = deriv (a : ℝ → ℂ) 0 + deriv (b : ℝ → ℂ) 0 := by
    rintro ⟨a, -, va, hva⟩ ⟨b, -, vb, hvb⟩
    rw [(hva.add hq hvb).deriv_eq, hva.deriv_eq, hvb.deriv_eq]
    rfl
  have hderiv_smul : ∀ (c : ℂ) (a : deficiencySpace q hq z),
      deriv (c • (a : ℝ → ℂ)) 0 = c * deriv (a : ℝ → ℂ) 0 := by
    rintro c ⟨a, -, va, hva⟩
    rw [(hva.smul c).deriv_eq, hva.deriv_eq]
    rfl
  set φ : deficiencySpace q hq z →ₗ[ℂ] ℂ × ℂ :=
    { toFun := fun a => ((a : ℝ → ℂ) 0, deriv (a : ℝ → ℂ) 0)
      map_add' := by
        intro a b
        exact Prod.ext rfl (hderiv_add a b)
      map_smul' := by
        intro c a
        exact Prod.ext rfl (hderiv_smul c a) }
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, ha⟩ h
    have h1 : a 0 = 0 := congrArg Prod.fst h
    have h2 : deriv a 0 = 0 := congrArg Prod.snd h
    exact Subtype.ext (huniq a ha h1 h2)
  calc Module.rank ℂ (deficiencySpace q hq z) ≤ Module.rank ℂ (ℂ × ℂ) :=
        LinearMap.rank_le_of_injective φ hinj
    _ = 2 := by simp [one_add_one_eq_two]

end Brockian.Weyl.DeficiencyODE

