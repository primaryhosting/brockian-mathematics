/-
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Stone's theorem: the generator of a strongly continuous one-parameter unitary group

Let `H` be a complex Hilbert space and let `U : ℝ → H →L[ℂ] H` be a strongly continuous
one-parameter unitary group, i.e. `U 0 = 1`, `U (s + t) = U s * U t`, every `U t` is unitary,
and `t ↦ U t x` is continuous for every `x`.

The *generator* of `U` is the (in general unbounded) operator `A` whose domain consists of the
vectors `x` for which `t ↦ U t x` is differentiable at `0`, and which is given there by
`A x = -I • (d/dt)|_{t = 0} (U t x)`, so that formally `U t = exp (I * t * A)`.

The main result, `QPhys.stone_generator`, is that `A` is self-adjoint as a partially defined
operator (`LinearPMap`).

The proof follows the classical argument:

* `A` is symmetric, by differentiating `t ↦ ⟪U t x, U t y⟫`;
* `A ± I` are surjective, using the resolvent `x ↦ ∫ t in Ioi 0, exp (-t) • U t x`;
* consequently the domain of `A` is dense, and every symmetric operator with `A ± I` surjective
  is self-adjoint.
-/

open MeasureTheory Set

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The domain of the (infinitesimal) generator of a one-parameter family `U : ℝ → H →L[ℂ] H`:
the set of vectors `x` for which `t ↦ U t x` is differentiable at `0`. -/
def genDomain (U : ℝ → H →L[ℂ] H) : Submodule ℂ H where
  carrier := {x | ∃ y, HasDerivAt (fun t : ℝ => U t x) y 0}
  add_mem' := by
    rintro a b ⟨ya, ha⟩ ⟨yb, hb⟩
    exact ⟨ya + yb, by simpa [map_add] using ha.add hb⟩
  zero_mem' := ⟨0, by simpa using hasDerivAt_const (0 : ℝ) (0 : H)⟩
  smul_mem' := by
    rintro c a ⟨ya, ha⟩
    exact ⟨c • ya, by simpa [map_smul] using ha.const_smul c⟩

theorem mem_genDomain_iff {U : ℝ → H →L[ℂ] H} {x : H} :
    x ∈ genDomain U ↔ ∃ y, HasDerivAt (fun t : ℝ => U t x) y 0 := Iff.rfl

/-- The derivative at `0` of `t ↦ U t x`, for `x` in the domain of the generator. -/
noncomputable def genDeriv (U : ℝ → H →L[ℂ] H) (x : genDomain U) : H := Classical.choose x.2

theorem genDeriv_spec (U : ℝ → H →L[ℂ] H) (x : genDomain U) :
    HasDerivAt (fun t : ℝ => U t (x : H)) (genDeriv U x) 0 := Classical.choose_spec x.2

theorem genDeriv_eq {U : ℝ → H →L[ℂ] H} (x : genDomain U) {y : H}
    (h : HasDerivAt (fun t : ℝ => U t (x : H)) y 0) : genDeriv U x = y :=
  (genDeriv_spec U x).unique h

/-- The generator of a one-parameter family, as a linear map on `genDomain U`.
It is `-I` times the derivative at `0`, so that (formally) `U t = exp (I * t * A)`. -/
noncomputable def genLinear (U : ℝ → H →L[ℂ] H) : genDomain U →ₗ[ℂ] H where
  toFun x := -Complex.I • genDeriv U x
  map_add' x y := by
    have : genDeriv U (x + y) = genDeriv U x + genDeriv U y := by
      refine genDeriv_eq _ ?_
      simpa [map_add] using (genDeriv_spec U x).add (genDeriv_spec U y)
    rw [this, smul_add]
  map_smul' c x := by
    have : genDeriv U (c • x) = c • genDeriv U x := by
      refine genDeriv_eq _ ?_
      simpa [map_smul] using (genDeriv_spec U x).const_smul c
    rw [this]
    simp only [RingHom.id_apply]
    exact smul_comm _ _ _

theorem genLinear_of_hasDerivAt {U : ℝ → H →L[ℂ] H} {x : H} (hx : x ∈ genDomain U) {d : H}
    (h : HasDerivAt (fun t : ℝ => U t x) d 0) :
    genLinear U ⟨x, hx⟩ = -Complex.I • d := by
  show -Complex.I • genDeriv U ⟨x, hx⟩ = _
  rw [genDeriv_eq ⟨x, hx⟩ h]

/-- The generator of a strongly continuous one-parameter unitary group, as an unbounded
(partially defined) operator. -/
noncomputable def gen (U : ℝ → H →L[ℂ] H) : H →ₗ.[ℂ] H := ⟨genDomain U, genLinear U⟩

@[simp] theorem gen_domain (U : ℝ → H →L[ℂ] H) : (gen U).domain = genDomain U := rfl

@[simp] theorem gen_apply (U : ℝ → H →L[ℂ] H) (x : genDomain U) :
    (gen U) x = genLinear U x := rfl

variable [CompleteSpace H]

/-- A strongly continuous one-parameter unitary group on a complex Hilbert space. -/
structure IsUnitaryGroup (U : ℝ → H →L[ℂ] H) : Prop where
  /-- `U 0` is the identity. -/
  map_zero : U 0 = 1
  /-- The group law. -/
  map_add : ∀ s t, U (s + t) = U s * U t
  /-- Every `U t` is a unitary operator. -/
  mem_unitary : ∀ t, U t ∈ unitary (H →L[ℂ] H)
  /-- Strong continuity. -/
  strongly_continuous : ∀ x : H, Continuous fun t : ℝ => U t x

namespace IsUnitaryGroup

variable {U : ℝ → H →L[ℂ] H}

theorem inner_map_map (hU : IsUnitaryGroup U) (t : ℝ) (x y : H) :
    inner ℂ (U t x) (U t y) = inner ℂ x y := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    show (star (U t)) (U t y) = (star (U t) * U t) y from rfl, (hU.mem_unitary t).1]
  simp

theorem norm_map (hU : IsUnitaryGroup U) (t : ℝ) (x : H) : ‖U t x‖ = ‖x‖ := by
  have h := hU.inner_map_map t x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : (‖U t x‖ : ℝ) ^ 2 = (‖x‖ : ℝ) ^ 2 := by exact_mod_cast h
  nlinarith [norm_nonneg (U t x), norm_nonneg x]

theorem star_eq (hU : IsUnitaryGroup U) (t : ℝ) : star (U t) = U (-t) := by
  have h2 : U t * U (-t) = 1 := by rw [← hU.map_add]; simp [hU.map_zero]
  calc star (U t) = star (U t) * (U t * U (-t)) := by rw [h2, mul_one]
    _ = star (U t) * U t * U (-t) := by rw [mul_assoc]
    _ = U (-t) := by rw [(hU.mem_unitary t).1, one_mul]

/-- The time-reversed group is again a strongly continuous one-parameter unitary group. -/
theorem neg (hU : IsUnitaryGroup U) : IsUnitaryGroup fun t => U (-t) where
  map_zero := by simpa using hU.map_zero
  map_add s t := by
    have : -(s + t) = -s + -t := by ring
    rw [this, hU.map_add]
  mem_unitary t := hU.mem_unitary (-t)
  strongly_continuous x := (hU.strongly_continuous x).comp continuous_neg

end IsUnitaryGroup

section Symmetric

variable {U : ℝ → H →L[ℂ] H}

/-- The basic symmetry relation: if `t ↦ U t x` and `t ↦ U t y` have derivatives `dx`, `dy`
at `0`, then `⟪x, dy⟫ + ⟪dx, y⟫ = 0`. -/
theorem inner_deriv_add_deriv_inner (hU : IsUnitaryGroup U) {x y dx dy : H}
    (hx : HasDerivAt (fun t : ℝ => U t x) dx 0) (hy : HasDerivAt (fun t : ℝ => U t y) dy 0) :
    inner ℂ x dy + inner ℂ dx y = (0 : ℂ) := by
  have hd := hx.inner ℂ hy
  have hconst : (fun t : ℝ => (inner ℂ (U t x) (U t y) : ℂ)) = fun _ => (inner ℂ x y : ℂ) :=
    funext fun t => hU.inner_map_map t x y
  rw [hconst] at hd
  have := (hasDerivAt_const (0 : ℝ) (inner ℂ x y : ℂ)).unique hd
  simpa [hU.map_zero] using this.symm

/-- The generator is a symmetric (formally self-adjoint) operator. -/
theorem gen_isFormalAdjoint (hU : IsUnitaryGroup U) : (gen U).IsFormalAdjoint (gen U) := by
  intro x y
  have h := inner_deriv_add_deriv_inner hU (genDeriv_spec U x) (genDeriv_spec U y)
  show inner ℂ (genLinear U x) ((y : H)) = inner ℂ ((x : H)) (genLinear U y)
  show inner ℂ (-Complex.I • genDeriv U x) ((y : H))
      = inner ℂ ((x : H)) (-Complex.I • genDeriv U y)
  rw [inner_smul_left, inner_smul_right]
  have h' : (inner ℂ (genDeriv U x) (y : H) : ℂ) = -inner ℂ (x : H) (genDeriv U y) := by
    linear_combination h
  rw [h']
  simp

end Symmetric

section Resolvent

variable {U : ℝ → H →L[ℂ] H}

/-- The resolvent vector `∫_0^∞ e^{-t} U t x dt`. -/
noncomputable def resolvent (U : ℝ → H →L[ℂ] H) (x : H) : H :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-t) • U t x

/-- The key computation: `t ↦ U t (resolvent U x)` is differentiable at `0` with derivative
`resolvent U x - x`. -/
theorem hasDerivAt_resolvent (hU : IsUnitaryGroup U) (x : H) :
    HasDerivAt (fun s : ℝ => U s (resolvent U x)) (resolvent U x - x) 0 := by
  set f : ℝ → H := fun t => Real.exp (-t) • U t x with hf
  have hfc : Continuous f :=
    (Real.continuous_exp.comp continuous_neg).smul (hU.strongly_continuous x)
  have hint : ∀ a : ℝ, IntegrableOn f (Ioi a) := by
    intro a
    refine Integrable.mono' (g := fun t : ℝ => Real.exp (-1 * t) * ‖x‖)
      ((exp_neg_integrableOn_Ioi a one_pos).mul_const ‖x‖) hfc.aestronglyMeasurable.restrict ?_
    filter_upwards with t
    simp [hf, norm_smul, hU.norm_map, Real.exp_nonneg, abs_of_nonneg]
  set R : H := ∫ t in Ioi (0 : ℝ), f t with hR
  set F : ℝ → H := fun s => ∫ t in (0 : ℝ)..s, f t with hFdef
  have hsplit : ∀ s : ℝ, ∫ u in Ioi s, f u = R - F s := by
    intro s
    rcases le_or_gt 0 s with hs | hs
    · have hunion : Ioi (0 : ℝ) = Ioc 0 s ∪ Ioi s := by rw [Ioc_union_Ioi_eq_Ioi hs]
      have h1 : R = (∫ u in Ioc (0 : ℝ) s, f u) + ∫ u in Ioi s, f u := by
        rw [hR, hunion, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
          ((hint 0).mono_set fun y hy => hy.1) (hint s)]
      rw [hFdef]
      simp only
      rw [intervalIntegral.integral_of_le hs, h1]
      abel
    · have hunion : Ioi s = Ioc s 0 ∪ Ioi (0 : ℝ) := by rw [Ioc_union_Ioi_eq_Ioi hs.le]
      have h1 : ∫ u in Ioi s, f u = (∫ u in Ioc s (0 : ℝ), f u) + R := by
        rw [hR, hunion, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
          ((hint s).mono_set fun y hy => hy.1) (hint 0)]
      rw [hFdef]
      simp only
      rw [intervalIntegral.integral_of_ge hs.le, h1]
      abel
  have htrans : ∀ (g : ℝ → H) (s : ℝ), ∫ t in Ioi (0 : ℝ), g (t + s) = ∫ u in Ioi s, g u := by
    intro g s
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    have h : ∀ t : ℝ,
        (Ioi (0 : ℝ)).indicator (fun t => g (t + s)) t = (Ioi s).indicator g (t + s) := by
      intro t
      by_cases h : t ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem h, indicator_of_mem (show t + s ∈ Ioi s by simpa using h)]
      · rw [indicator_of_notMem h, indicator_of_notMem (show t + s ∉ Ioi s by simpa using h)]
    simp_rw [h]
    exact integral_add_right_eq_self (fun u => (Ioi s).indicator g u) s
  have key : ∀ s : ℝ, U s R = Real.exp s • (R - F s) := by
    intro s
    have h1 : U s R = ∫ t in Ioi (0 : ℝ), Real.exp s • f (t + s) := by
      rw [hR, ← ContinuousLinearMap.integral_comp_comm _ (hint 0)]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [hf]
      simp only
      rw [ContinuousLinearMap.map_smul_of_tower, smul_smul]
      have e1 : Real.exp s * Real.exp (-(t + s)) = Real.exp (-t) := by
        rw [← Real.exp_add]; ring_nf
      have e2 : U (t + s) x = U s (U t x) := by rw [add_comm, hU.map_add]; rfl
      rw [e1, e2]
    rw [h1, integral_smul, htrans f s, hsplit s]
  have hF : HasDerivAt F (f 0) 0 :=
    intervalIntegral.integral_hasDerivAt_right (hfc.intervalIntegrable _ _)
      (hfc.stronglyMeasurableAtFilter _ _) hfc.continuousAt
  have hF0 : F 0 = 0 := by simp [hFdef]
  have hf0 : f 0 = x := by simp [hf, hU.map_zero]
  have hd : HasDerivAt (fun s : ℝ => Real.exp s • (R - F s))
      (Real.exp 0 • (0 - f 0) + Real.exp 0 • (R - F 0)) 0 :=
    (Real.hasDerivAt_exp 0).smul ((hasDerivAt_const (0 : ℝ) R).sub hF)
  have heq : Real.exp 0 • (0 - f 0) + Real.exp 0 • (R - F 0) = R - x := by
    rw [hF0, hf0]; simp; abel
  rw [heq] at hd
  have hfun : (fun s : ℝ => U s R) = fun s : ℝ => Real.exp s • (R - F s) := funext key
  show HasDerivAt (fun s : ℝ => U s R) (R - x) 0
  rw [hfun]
  exact hd

theorem resolvent_mem_genDomain (hU : IsUnitaryGroup U) (x : H) :
    resolvent U x ∈ genDomain U := ⟨_, hasDerivAt_resolvent hU x⟩

/-- Surjectivity of `A + I`. -/
theorem exists_gen_add_I (hU : IsUnitaryGroup U) (y : H) :
    ∃ w : genDomain U, genLinear U w + Complex.I • (w : H) = y := by
  set x : H := -Complex.I • y with hx
  have hmem := resolvent_mem_genDomain hU x
  refine ⟨⟨resolvent U x, hmem⟩, ?_⟩
  rw [genLinear_of_hasDerivAt hmem (hasDerivAt_resolvent hU x)]
  have h1 : -Complex.I • (resolvent U x - x) + Complex.I • resolvent U x = Complex.I • x := by
    module
  rw [h1, hx, smul_smul]
  simp

/-- Surjectivity of `A - I`. -/
theorem exists_gen_sub_I (hU : IsUnitaryGroup U) (y : H) :
    ∃ w : genDomain U, genLinear U w - Complex.I • (w : H) = y := by
  set x : H := Complex.I • y with hx
  set V : ℝ → H →L[ℂ] H := fun t => U (-t) with hV
  have hd : HasDerivAt (fun s : ℝ => U (-s) (resolvent V x)) (resolvent V x - x) 0 :=
    hasDerivAt_resolvent hU.neg x
  -- reverse time
  have hneg : HasDerivAt (fun t : ℝ => -t) (-1 : ℝ) 0 := (hasDerivAt_id 0).neg
  have hd2 : HasDerivAt (fun s : ℝ => U s (resolvent V x)) (x - resolvent V x) 0 := by
    have hd' : HasDerivAt (fun s : ℝ => U (-s) (resolvent V x)) (resolvent V x - x) (-(0 : ℝ)) := by
      rwa [neg_zero]
    have := HasDerivAt.scomp (0 : ℝ) hd' hneg
    simp only [Function.comp_def, neg_neg] at this
    have heq : (-1 : ℝ) • (resolvent V x - x) = x - resolvent V x := by module
    rwa [heq] at this
  have hmem : resolvent V x ∈ genDomain U := ⟨_, hd2⟩
  refine ⟨⟨resolvent V x, hmem⟩, ?_⟩
  rw [genLinear_of_hasDerivAt hmem hd2]
  have h1 : -Complex.I • (x - resolvent V x) - Complex.I • resolvent V x = -Complex.I • x := by
    module
  rw [h1, hx, smul_smul]
  simp

end Resolvent

section Main

variable {U : ℝ → H →L[ℂ] H}

/-- The domain of the generator is dense. -/
theorem dense_genDomain (hU : IsUnitaryGroup U) :
    Dense ((genDomain U : Submodule ℂ H) : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  refine Submodule.orthogonal_eq_bot_iff.mp ?_
  rw [Submodule.eq_bot_iff]
  intro y hy
  have hy' : ∀ v ∈ genDomain U, inner ℂ v y = (0 : ℂ) := fun v hv =>
    hy v (Submodule.le_topologicalClosure _ hv)
  obtain ⟨w, hw⟩ := exists_gen_add_I hU y
  have h0 : inner ℂ (w : H) y = (0 : ℂ) := hy' w w.2
  rw [← hw, inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K] at h0
  have hsymm : inner ℂ (genLinear U w) (w : H) = inner ℂ (w : H) (genLinear U w) :=
    gen_isFormalAdjoint hU w w
  have him : (inner ℂ (w : H) (genLinear U w) : ℂ).im = 0 := by
    rw [← Complex.conj_eq_iff_im, inner_conj_symm]
    exact hsymm
  have hn : ‖(w : H)‖ = 0 := by
    have h1 := congrArg Complex.im h0
    simp [Complex.add_im, Complex.mul_im, him] at h1
    have h2 : ‖(w : H)‖ ^ 2 = 0 := by exact_mod_cast h1
    exact (pow_eq_zero_iff two_ne_zero).mp h2
  have hw0 : (w : H) = 0 := by simpa using hn
  have hwz : w = 0 := Subtype.ext hw0
  rw [← hw, hwz]
  simp

/-- The adjoint of the generator is contained in the generator: this is the maximality half
of self-adjointness. -/
theorem adjoint_le_gen (hU : IsUnitaryGroup U) : (gen U).adjoint ≤ gen U := by
  have hdense : Dense ((gen U).domain : Set H) := dense_genDomain hU
  have hfa := LinearPMap.adjoint_isFormalAdjoint (T := gen U) hdense
  have main : ∀ y : (gen U).adjoint.domain, ∃ w : genDomain U,
      (w : H) = (y : H) ∧ genLinear U w = (gen U).adjoint y := by
    intro y
    obtain ⟨w, hw⟩ := exists_gen_sub_I hU ((gen U).adjoint y - Complex.I • (y : H))
    have hAv : ∀ v : genDomain U,
        inner ℂ (genLinear U v) ((y : H)) = inner ℂ (v : H) ((gen U).adjoint y) := by
      intro v
      rw [← inner_conj_symm (v : H) ((gen U).adjoint y), hfa y v, inner_conj_symm]
      rfl
    have hperp : ∀ v : genDomain U,
        inner ℂ (genLinear U v + Complex.I • (v : H)) ((y : H) - (w : H)) = (0 : ℂ) := by
      intro v
      have e1 : inner ℂ (genLinear U v + Complex.I • (v : H)) ((y : H))
          = inner ℂ (v : H) ((gen U).adjoint y - Complex.I • (y : H)) := by
        rw [inner_add_left, inner_smul_left, hAv v, inner_sub_right, inner_smul_right]
        simp [Complex.conj_I]
        ring
      have hsym : inner ℂ (genLinear U v) (w : H) = inner ℂ (v : H) (genLinear U w) :=
        gen_isFormalAdjoint hU v w
      have e2 : inner ℂ (genLinear U v + Complex.I • (v : H)) ((w : H))
          = inner ℂ (v : H) (genLinear U w - Complex.I • (w : H)) := by
        rw [inner_add_left, inner_smul_left, hsym, inner_sub_right, inner_smul_right]
        simp [Complex.conj_I]
        ring
      rw [inner_sub_right, e1, e2, hw, sub_self]
    have hzero : (y : H) - (w : H) = 0 := by
      obtain ⟨u, hu⟩ := exists_gen_add_I hU ((y : H) - (w : H))
      have h := hperp u
      rw [hu] at h
      exact inner_self_eq_zero.mp h
    have hyw : (w : H) = (y : H) := (sub_eq_zero.mp hzero).symm
    refine ⟨w, hyw, ?_⟩
    have hrw : genLinear U w
        = ((gen U).adjoint y - Complex.I • (y : H)) + Complex.I • (w : H) := by
      rw [← hw]; abel
    rw [hrw, hyw]
    abel
  refine ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨w, h1, _⟩ := main ⟨v, hv⟩
    have h2 := w.2
    rw [h1] at h2
    exact h2
  · intro a b hab
    obtain ⟨w, h1, h2⟩ := main a
    have hb : b = (⟨(w : H), w.2⟩ : genDomain U) := by
      apply Subtype.ext
      rw [← hab, ← h1]
    show (gen U).adjoint a = gen U b
    rw [hb, ← h2]
    rfl

/-- Stone's theorem: the generator of a strongly continuous one-parameter unitary group
is self-adjoint. -/
theorem stone_generator (U : ℝ → H →L[ℂ] H) (hU0 : U 0 = 1)
    (hUadd : ∀ s t, U (s + t) = U s * U t)
    (hUunit : ∀ t, U t ∈ unitary (H →L[ℂ] H))
    (hUcont : ∀ x : H, Continuous fun t : ℝ => U t x) :
    IsSelfAdjoint (gen U) := by
  have hU : IsUnitaryGroup U := ⟨hU0, hUadd, hUunit, hUcont⟩
  have hdense : Dense ((gen U).domain : Set H) := dense_genDomain hU
  rw [LinearPMap.isSelfAdjoint_def]
  exact le_antisymm (adjoint_le_gen hU) ((gen_isFormalAdjoint hU).le_adjoint hdense)

end Main

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

